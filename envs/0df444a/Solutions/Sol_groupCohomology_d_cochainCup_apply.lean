-- Prove2me | solution 1 for groupCohomology.d_cochainCup_apply
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/8262b390-207c-54e1-bfe9-454178393353

import Mathlib
import Definitions.Def_GroupCohomology_CochainCup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_d_cochainCup_apply

set_option autoImplicit false
universe u
p2m_open "CategoryTheory CategoryTheory.MonoidalCategory groupCohomology"

namespace P2mS26Cup

variable {G : Type u} {p q : ℕ}

theorem fst_succ (σ : Fin (p + q + 1) → G) :
    cochainCupFst p q (fun i => σ i.succ) = fun i => cochainCupFst (p + 1) q (fun i => σ (Fin.cast (Nat.add_right_comm p 1 q) i)) i.succ := by
  funext x
  exact congrArg σ (Fin.ext (by simp))

theorem snd_succ (σ : Fin (p + q + 1) → G) :
    cochainCupSnd p q (fun i => σ i.succ) = cochainCupSnd (p + 1) q (fun i => σ (Fin.cast (Nat.add_right_comm p 1 q) i)) := by
  funext x
  exact congrArg σ (Fin.ext (by simp; omega))

theorem hd_zero (σ : Fin (p + q + 1) → G) : cochainCupFst (p + 1) q (fun i => σ (Fin.cast (Nat.add_right_comm p 1 q) i)) 0 = σ 0 :=
  congrArg σ (Fin.ext (by simp))

theorem partialProd_hd_succ [Monoid G] (σ : Fin (p + q + 1) → G) :
    σ 0 * Fin.partialProd (cochainCupFst p q (fun i => σ i.succ)) (Fin.last p)
      = Fin.partialProd (cochainCupFst (p + 1) q (fun i => σ (Fin.cast (Nat.add_right_comm p 1 q) i))) (Fin.last (p + 1)) := by
  rw [← Fin.succ_last, Fin.partialProd_succ', fst_succ, hd_zero]
  rfl

theorem fst_contractNth_castAdd [Mul G] (σ : Fin (p + q + 1) → G) (j : Fin p) :
    cochainCupFst p q (Fin.contractNth (Fin.castAdd (q + 1) j) (· * ·) σ)
      = Fin.contractNth (Fin.castSucc j) (· * ·) (cochainCupFst (p + 1) q (fun i => σ (Fin.cast (Nat.add_right_comm p 1 q) i))) := by
  funext x
  simp only [cochainCupFst, Fin.contractNth, Fin.val_castAdd, Fin.val_castSucc]
  split_ifs <;> first | omega | rfl

theorem snd_contractNth_castAdd [Mul G] (σ : Fin (p + q + 1) → G) (j : Fin p) :
    cochainCupSnd p q (Fin.contractNth (Fin.castAdd (q + 1) j) (· * ·) σ) = cochainCupSnd (p + 1) q (fun i => σ (Fin.cast (Nat.add_right_comm p 1 q) i)) := by
  funext x
  simp only [cochainCupSnd, Fin.contractNth, Fin.val_castAdd, Fin.val_natAdd]
  split_ifs <;> first | omega | exact congrArg σ (Fin.ext (by simp; omega))

theorem partialProd_contractNth_castSucc [Monoid G] (τ : Fin (p + 1) → G) (j : Fin p) :
    Fin.partialProd (Fin.contractNth (Fin.castSucc j) (· * ·) τ) (Fin.last p)
      = Fin.partialProd τ (Fin.last (p + 1)) := by
  rw [Fin.partialProd_contractNth, Function.comp_apply, Fin.succAbove_of_le_castSucc _ _
    (by simp only [Fin.le_iff_val_le_val, Fin.val_succ, Fin.val_castSucc, Fin.val_last]; omega),
    Fin.succ_last]

theorem fst_contractNth_natAdd [Mul G] (σ : Fin (p + q + 1) → G) (i : Fin (q + 1)) :
    cochainCupFst p q (Fin.contractNth (Fin.natAdd p i) (· * ·) σ) = cochainCupFst p (q + 1) σ := by
  funext x
  simp only [cochainCupFst, Fin.contractNth, Fin.val_castAdd, Fin.val_natAdd]
  split_ifs <;> first | omega | exact congrArg σ (Fin.ext (by simp))

theorem snd_contractNth_natAdd [Mul G] (σ : Fin (p + q + 1) → G) (i : Fin (q + 1)) :
    cochainCupSnd p q (Fin.contractNth (Fin.natAdd p i) (· * ·) σ)
      = Fin.contractNth i (· * ·) (cochainCupSnd p (q + 1) σ) := by
  funext x
  simp only [cochainCupSnd, Fin.contractNth, Fin.val_natAdd]
  split_ifs <;> first | omega | rfl

theorem contractNth_last_hd [Mul G] (σ : Fin (p + q + 1) → G) :
    Fin.contractNth (Fin.last p) (· * ·) (cochainCupFst (p + 1) q (fun i => σ (Fin.cast (Nat.add_right_comm p 1 q) i))) = cochainCupFst p (q + 1) σ := by
  funext x
  rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simp)]
  rfl

theorem partialProd_hd_last [Monoid G] (σ : Fin (p + q + 1) → G) :
    Fin.partialProd (cochainCupFst p (q + 1) σ) (Fin.last p) * cochainCupSnd p (q + 1) σ 0
      = Fin.partialProd (cochainCupFst (p + 1) q (fun i => σ (Fin.cast (Nat.add_right_comm p 1 q) i))) (Fin.last (p + 1)) := by
  rw [← Fin.succ_last, Fin.partialProd_succ, ← Fin.partialProd_init]
  rfl

theorem tail_tl (σ : Fin (p + q + 1) → G) : (fun j => cochainCupSnd p (q + 1) σ j.succ) = cochainCupSnd (p + 1) q (fun i => σ (Fin.cast (Nat.add_right_comm p 1 q) i)) := by
  funext x
  exact congrArg σ (Fin.ext (by simp; omega))

theorem dsum_castSucc {k : Type u} [CommRing k] {V : Type u} [AddCommGroup V] [Module k V] [Mul G]
    (f : (Fin p → G) → V) (τ : Fin (p + 1) → G) :
    ∑ j : Fin (p + 1), (-1 : k) ^ ((j : ℕ) + 1) • f (Fin.contractNth j (· * ·) τ)
      = ∑ j : Fin p, (-1 : k) ^ ((j : ℕ) + 1) • f (Fin.contractNth (Fin.castSucc j) (· * ·) τ)
        + (-1 : k) ^ (p + 1) • f (Fin.contractNth (Fin.last p) (· * ·) τ) := by
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]

theorem sum_split {M : Type*} [AddCommMonoid M] (p q : ℕ) (F : Fin (p + q + 1) → M) :
    ∑ j, F j = ∑ j : Fin p, F (Fin.castAdd (q + 1) j) + ∑ i : Fin (q + 1), F (Fin.natAdd p i) :=
  Fin.sum_univ_add (a := p) (b := q + 1) F

theorem tensor_ρ_tmul {k : Type u} [CommRing k] [Group G] (A B : Rep.{u} k G) (s : G) (a : A) (b : B) :
    (A ⊗ B).ρ s (a ⊗ₜ[k] b) = A.ρ s a ⊗ₜ[k] B.ρ s b := by
  rw [Rep.tensor_ρ]
  rfl

theorem ρ_ρ {k : Type u} [CommRing k] [Group G] (B : Rep.{u} k G) (s t : G) (b : B) :
    B.ρ s (B.ρ t b) = B.ρ (s * t) b := by
  rw [map_mul]
  rfl

end P2mS26Cup

open P2mS26Cup in
theorem solution {k G : Type u} [CommRing k] [Group G] (A B : Rep.{u} k G) (p q : ℕ)
    (f : (Fin p → G) → A) (g : (Fin q → G) → B) (σ : Fin (p + q + 1) → G) :
    (inhomogeneousCochains.d (A ⊗ B) (p + q)).hom (groupCohomology.cochainCup A B p q f g) σ
      = groupCohomology.cochainCup A B (p + 1) q ((inhomogeneousCochains.d A p).hom f) g
          (fun i => σ (Fin.cast (Nat.add_right_comm p 1 q) i))
        + ((-1 : k) ^ p) • groupCohomology.cochainCup A B p (q + 1) f ((inhomogeneousCochains.d B q).hom g) σ := by
  simp only [cochainCup_apply, inhomogeneousCochains.d_hom_apply]
  rw [sum_split, tensor_ρ_tmul, ρ_ρ, partialProd_hd_succ, fst_succ, snd_succ, hd_zero, dsum_castSucc,
    contractNth_last_hd]
  simp only [fst_contractNth_castAdd, snd_contractNth_castAdd, partialProd_contractNth_castSucc,
    fst_contractNth_natAdd, snd_contractNth_natAdd, Fin.val_castAdd, Fin.val_natAdd]
  simp only [TensorProduct.add_tmul, TensorProduct.sum_tmul, ← TensorProduct.smul_tmul', map_add, map_sum,
    map_smul, TensorProduct.tmul_add, TensorProduct.tmul_sum, TensorProduct.tmul_smul, smul_add, Finset.smul_sum,
    smul_smul]
  rw [ρ_ρ, partialProd_hd_last, tail_tl]
  simp only [pow_add, pow_one, mul_neg, mul_one, neg_smul]
  abel

end S_groupCohomology_d_cochainCup_apply
end P2MW
export P2MW.S_groupCohomology_d_cochainCup_apply (solution)
