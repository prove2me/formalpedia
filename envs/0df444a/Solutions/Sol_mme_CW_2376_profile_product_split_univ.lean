-- Prove2me | solution 1 for mme_CW_2376_profile_product_split_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T18:05:09.759588+00:00
-- url     : https://prove2.me/submissions/8dee488d-1021-4def-bc22-7378e719ead3

import Definitions.Def_mme_CW_2376_address_block
import Definitions.Def_mme_rank_bridge

open MME BigOperators

set_option autoImplicit false
set_option maxRecDepth 100000

universe v

private def profileCat (σ : Fin 3 → Fin 5) : Fin 5 :=
  if σ ∈ cw2376ScalarTypes then 0
  else if σ ∈ cw2376RectTypes then 1
  else if σ ∈ cw2376CentralTypes then 2
  else if σ ∈ cw2376CoupledTypes then 3
  else 4

private def profileExp (m : ℕ) : Fin 5 → ℕ
  | 0 => 699 * m
  | 1 => 37518 * m
  | 2 => 307638 * m
  | 3 => 616627 * m
  | _ => 0

private theorem profileMultiplicity_eq_exp_cat (m : ℕ) (σ : Fin 3 → Fin 5) :
    cw2376ProfileMultiplicity m σ = profileExp m (profileCat σ) := by
  simp only [cw2376ProfileMultiplicity, profileCat]
  split_ifs <;> rfl

theorem solution {M : Type v} [CommMonoid M]
    (Q : (Fin 3 → Fin 5) → M) (m : ℕ) :
    (∏ σ, Q σ ^ cw2376ProfileMultiplicity m σ) =
      (∏ σ ∈ cw2376ScalarTypes, Q σ) ^ (699 * m) *
      (∏ σ ∈ cw2376RectTypes, Q σ) ^ (37518 * m) *
      (∏ σ ∈ cw2376CentralTypes, Q σ) ^ (307638 * m) *
      (∏ σ ∈ cw2376CoupledTypes, Q σ) ^ (616627 * m) := by
  classical
  have h0 :
      Finset.univ.filter (fun σ : Fin 3 → Fin 5 => profileCat σ = 0) =
        cw2376ScalarTypes := by decide
  have h1 :
      Finset.univ.filter (fun σ : Fin 3 → Fin 5 => profileCat σ = 1) =
        cw2376RectTypes := by decide
  have h2 :
      Finset.univ.filter (fun σ : Fin 3 → Fin 5 => profileCat σ = 2) =
        cw2376CentralTypes := by decide
  have h3 :
      Finset.univ.filter (fun σ : Fin 3 → Fin 5 => profileCat σ = 3) =
        cw2376CoupledTypes := by decide
  calc
    (∏ σ, Q σ ^ cw2376ProfileMultiplicity m σ) =
        ∏ σ, Q σ ^ profileExp m (profileCat σ) := by
          apply Finset.prod_congr rfl
          intro σ _
          rw [profileMultiplicity_eq_exp_cat]
    _ = ∏ c : Fin 5,
        ∏ σ ∈ Finset.univ with profileCat σ = c,
          Q σ ^ profileExp m (profileCat σ) := by
          symm
          exact Finset.prod_fiberwise Finset.univ profileCat
            (fun σ => Q σ ^ profileExp m (profileCat σ))
    _ = ∏ c : Fin 5,
        (∏ σ ∈ Finset.univ with profileCat σ = c, Q σ) ^
          profileExp m c := by
          apply Finset.prod_congr rfl
          intro c _
          rw [← Finset.prod_pow]
          apply Finset.prod_congr rfl
          intro σ hσ
          rw [(Finset.mem_filter.mp hσ).2]
    _ = _ := by
      rw [Fin.prod_univ_five]
      simp only [profileExp, h0, h1, h2, h3, pow_zero, mul_one]
