-- Prove2me | solution 1 for mme_dwz_table2_121_211_rows_six_symmetric_finite_extraction_sqrt_loss
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T13:36:30.818261+00:00
-- url     : https://prove2.me/submissions/9bc56625-13f4-4f3b-9403-5c4a9c665a44

import Mathlib
import Theorems.Thm_mme_CW_q6_primary_hash_sqrt_capacity_bounded
import Theorems.Thm_mme_dwz_q6_121_normalized_restricted_primary_hash_Ctensor_certificate
import Theorems.Thm_mme_dwz_q6_211_normalized_restricted_primary_hash_Ctensor_certificate
import Theorems.Thm_mme_dwz_q6_assemble_one_half_pointwise
import Theorems.Thm_mme_sixSymmetrization_isomorphic_cyclic_orbit
import Theorems.Thm_mme_dwz_q6_121_211_componentBase_cube
import Definitions.Def_mme_dwz_square_data

open MME BigOperators Filter Topology
open MME.DWZSquare MME.DWZComponentRestriction

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000

namespace P2M867

def CapacityWitness (tau C : ℝ) (N : ℕ) : Prop :=
  let lambda : ℝ := 2 / ((6 : ℝ) ^ (3 * tau) + 2)
  let L : ℕ := ⌊lambda * (N : ℝ)⌋₊
  let G : ℕ := N - L
  let side : ℕ := 36 ^ (2 * G) * 6 ^ (2 * L)
  let raw : ℝ :=
    4 * (6 : ℝ) ^ (3 * tau) * ((6 : ℝ) ^ (3 * tau) + 2)
  ∃ A H : ℕ,
    ∃ _family : CWQ6PrimaryHashFamily N L G A H,
      H ≤ 4 ^ N ∧
      raw ^ (2 * N) *
          Real.exp (-C * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
        (((A ^ 3 : ℕ) : ℝ) * (H : ℝ) ^ 2) *
          ((((side * side * side : ℕ) : ℝ)) ^ tau)

def ExtractionGoal
    (K : Type u) [Field K] (tau C : ℝ) (m : ℕ) : Prop :=
  ∀ s : Fin 15, (s = 13 ∨ s = 14) →
    ∃ (q : ℕ) (A B Cdim : Fin q → ℕ),
      TensorObj.Restrict
        (TensorObj.bigAdd (fun j ↦ MMObj K (A j) (B j) (Cdim j)))
        (sixSymmetrization (restrictedComponentPower K s m)) ∧
      (4 * (6 : ℝ) ^ (3 * tau) *
          ((6 : ℝ) ^ (3 * tau) + 2)) ^
            (2 * (MME.DWZTable2Counts.component s * m)) *
          Real.exp (-C * Real.sqrt
            (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))) ≤
        ∑ j, (((A j * B j * Cdim j : ℕ) : ℝ) ^ tau)

theorem rate_transport
    (raw C x y S : ℝ) (N R : ℕ)
    (hraw : 0 ≤ raw) (hC : 0 ≤ C) (hxy : x ≤ y)
    (hR : R = 2 * N)
    (hweight : raw ^ (4 * N) * Real.exp (-C * x) ≤ S) :
    raw ^ (2 * R) * Real.exp (-C * y) ≤ S := by
  have hexp : Real.exp (-C * y) ≤ Real.exp (-C * x) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    raw ^ (2 * R) * Real.exp (-C * y) =
        raw ^ (4 * N) * Real.exp (-C * y) := by
      rw [hR]
      congr 2
      omega
    _ ≤ raw ^ (4 * N) * Real.exp (-C * x) :=
      mul_le_mul_of_nonneg_left hexp (pow_nonneg hraw _)
    _ ≤ S := hweight

theorem normalized_pointwise
    {K : Type u} [Field K]
    (tau C₀ : ℝ) (N L G A H : ℕ) (S T : TensorObj K 3)
    (stars : CTensorOneHOneFamilyCertificate
      S A H (6 ^ (4 * G + 2 * L)))
    (hHbound : H ≤ 4 ^ N)
    (hnormalize : TensorObj.Restrict (sixSymmetrization S) T)
    (hrate :
      (4 * (6 : ℝ) ^ (3 * tau) * ((6 : ℝ) ^ (3 * tau) + 2)) ^
            (2 * N) *
          Real.exp (-C₀ * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
        (((A ^ 3 : ℕ) : ℝ) * (H : ℝ) ^ 2) *
          (((((36 ^ (2 * G) * 6 ^ (2 * L)) *
            (36 ^ (2 * G) * 6 ^ (2 * L)) *
            (36 ^ (2 * G) * 6 ^ (2 * L)) : ℕ) : ℝ)) ^ tau)) :
    ∃ (q : ℕ) (a b c : Fin q → ℕ),
      TensorObj.Restrict
        (TensorObj.bigAdd (fun j ↦ MMObj K (a j) (b j) (c j))) T ∧
      (4 * (6 : ℝ) ^ (3 * tau) * ((6 : ℝ) ^ (3 * tau) + 2)) ^
            (4 * N) *
          Real.exp (-(2 * C₀ + 400) *
            Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
        ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau) := by
  obtain ⟨q, a, b, c, hrestrict, hweight⟩ :=
    mme_dwz_q6_assemble_one_half_pointwise
      tau C₀ N L G A H S stars hHbound hrate
  exact ⟨q, a, b, c,
    TensorObj.Restrict.trans hrestrict hnormalize, hweight⟩

theorem row121_from_witness
    {K : Type u} [Field K]
    (tau C₀ : ℝ) (hC₀ : 0 ≤ C₀) (m : ℕ)
    (hWitness : CapacityWitness tau C₀
      (1036722900000000 * m)) :
    ∃ (q : ℕ) (A B Cdim : Fin q → ℕ),
      TensorObj.Restrict
        (TensorObj.bigAdd (fun j ↦ MMObj K (A j) (B j) (Cdim j)))
        (sixSymmetrization
          (restrictedComponentPower K (13 : Fin 15) m)) ∧
      (4 * (6 : ℝ) ^ (3 * tau) *
          ((6 : ℝ) ^ (3 * tau) + 2)) ^
            (2 * (MME.DWZTable2Counts.component (13 : Fin 15) * m)) *
          Real.exp (-(2 * C₀ + 400) * Real.sqrt
            (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))) ≤
        ∑ j, (((A j * B j * Cdim j : ℕ) : ℝ) ^ tau) := by
  dsimp only [CapacityWitness] at hWitness
  let halfCount : ℕ := 1036722900000000
  let N : ℕ := halfCount * m
  let lambda : ℝ := 2 / ((6 : ℝ) ^ (3 * tau) + 2)
  let L : ℕ := ⌊lambda * (N : ℝ)⌋₊
  let G : ℕ := N - L
  change ∃ A H : ℕ,
    ∃ family : CWQ6PrimaryHashFamily N L G A H,
      H ≤ 4 ^ N ∧
      (4 * (6 : ℝ) ^ (3 * tau) * ((6 : ℝ) ^ (3 * tau) + 2)) ^
            (2 * N) *
          Real.exp (-C₀ * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
        (((A ^ 3 : ℕ) : ℝ) * (H : ℝ) ^ 2) *
          (((((36 ^ (2 * G) * 6 ^ (2 * L)) *
            (36 ^ (2 * G) * 6 ^ (2 * L)) *
            (36 ^ (2 * G) * 6 ^ (2 * L)) : ℕ) : ℝ)) ^ tau) at hWitness
  obtain ⟨A, H, family, hHbound, hrate⟩ := hWitness
  obtain ⟨stars⟩ :=
    mme_dwz_q6_121_normalized_restricted_primary_hash_Ctensor_certificate
      (K := K) m L G A H (by simpa only [N, halfCount] using family)
  obtain ⟨q, a, b, c, hrestrict, hweight⟩ :=
    mme_dwz_q6_assemble_one_half_pointwise tau C₀ N L G A H
      (TensorObj.permObj cyclicPerm
        (restrictedComponentPower K (13 : Fin 15) m))
      stars hHbound hrate
  refine ⟨q, a, b, c,
    TensorObj.Restrict.trans hrestrict
      (mme_sixSymmetrization_isomorphic_cyclic_orbit
        (restrictedComponentPower K (13 : Fin 15) m)).1.1, ?_⟩
  let raw : ℝ :=
    4 * (6 : ℝ) ^ (3 * tau) * ((6 : ℝ) ^ (3 * tau) + 2)
  let C : ℝ := 2 * C₀ + 400
  let x : ℝ := Real.sqrt (((N + 1 : ℕ) : ℝ))
  let y : ℝ := Real.sqrt
    (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))
  let R : ℕ := MME.DWZTable2Counts.component (13 : Fin 15) * m
  have hraw : 0 ≤ raw := by dsimp only [raw]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hscale : N + 1 ≤ MME.DWZTable2Counts.scale * m + 1 := by
    dsimp only [N, halfCount, MME.DWZTable2Counts.scale]
    omega
  have hxy : x ≤ y := by
    dsimp only [x, y]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hscale)
  have hR : R = 2 * N := by
    change 2073445800000000 * m =
      2 * (1036722900000000 * m)
    ring
  exact rate_transport
    raw C x y (∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau)) N R
      hraw hC hxy hR (by simpa only [raw, C, x] using hweight)

theorem row211_pointwise_from_family
    {K : Type u} [Field K]
    (tau C₀ : ℝ) (m L G A H : ℕ)
    (family : CWQ6PrimaryHashFamily
      (1036722900000000 * m) L G A H)
    (hHbound : H ≤ 4 ^ (1036722900000000 * m))
    (hrate :
      (4 * (6 : ℝ) ^ (3 * tau) * ((6 : ℝ) ^ (3 * tau) + 2)) ^
            (2 * (1036722900000000 * m)) *
          Real.exp (-C₀ * Real.sqrt
            ((((1036722900000000 * m) + 1 : ℕ) : ℝ))) ≤
        (((A ^ 3 : ℕ) : ℝ) * (H : ℝ) ^ 2) *
          (((((36 ^ (2 * G) * 6 ^ (2 * L)) *
            (36 ^ (2 * G) * 6 ^ (2 * L)) *
            (36 ^ (2 * G) * 6 ^ (2 * L)) : ℕ) : ℝ)) ^ tau)) :
    ∃ (q : ℕ) (a b c : Fin q → ℕ),
      TensorObj.Restrict
        (TensorObj.bigAdd (fun j ↦ MMObj K (a j) (b j) (c j)))
        (sixSymmetrization
          (restrictedComponentPower K (14 : Fin 15) m)) ∧
      (4 * (6 : ℝ) ^ (3 * tau) * ((6 : ℝ) ^ (3 * tau) + 2)) ^
            (4 * (1036722900000000 * m)) *
          Real.exp (-(2 * C₀ + 400) * Real.sqrt
            ((((1036722900000000 * m) + 1 : ℕ) : ℝ))) ≤
        ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau) := by
  obtain ⟨stars⟩ :=
    mme_dwz_q6_211_normalized_restricted_primary_hash_Ctensor_certificate
      (K := K) m L G A H family
  exact normalized_pointwise
    tau C₀ (1036722900000000 * m) L G A H
    (TensorObj.permObj (cyclicPerm.trans cyclicPerm)
      (restrictedComponentPower K (14 : Fin 15) m))
    (sixSymmetrization
      (restrictedComponentPower K (14 : Fin 15) m))
    stars hHbound
    (mme_sixSymmetrization_isomorphic_cyclic_orbit
      (restrictedComponentPower K (14 : Fin 15) m)).2.1
    hrate

theorem row211_from_witness
    {K : Type u} [Field K]
    (tau C₀ : ℝ) (hC₀ : 0 ≤ C₀) (m : ℕ)
    (hWitness : CapacityWitness tau C₀
      (1036722900000000 * m)) :
    ∃ (q : ℕ) (a b c : Fin q → ℕ),
      TensorObj.Restrict
        (TensorObj.bigAdd (fun j ↦ MMObj K (a j) (b j) (c j)))
        (sixSymmetrization
          (restrictedComponentPower K (14 : Fin 15) m)) ∧
      (4 * (6 : ℝ) ^ (3 * tau) *
          ((6 : ℝ) ^ (3 * tau) + 2)) ^
            (2 * (MME.DWZTable2Counts.component (14 : Fin 15) * m)) *
          Real.exp (-(2 * C₀ + 400) * Real.sqrt
            (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))) ≤
        ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau) := by
  dsimp only [CapacityWitness] at hWitness
  let N : ℕ := 1036722900000000 * m
  let lambda : ℝ := 2 / ((6 : ℝ) ^ (3 * tau) + 2)
  let L : ℕ := ⌊lambda * (N : ℝ)⌋₊
  let G : ℕ := N - L
  change ∃ A H : ℕ,
    ∃ family : CWQ6PrimaryHashFamily N L G A H,
      H ≤ 4 ^ N ∧
      (4 * (6 : ℝ) ^ (3 * tau) * ((6 : ℝ) ^ (3 * tau) + 2)) ^
            (2 * N) *
          Real.exp (-C₀ * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
        (((A ^ 3 : ℕ) : ℝ) * (H : ℝ) ^ 2) *
          (((((36 ^ (2 * G) * 6 ^ (2 * L)) *
            (36 ^ (2 * G) * 6 ^ (2 * L)) *
            (36 ^ (2 * G) * 6 ^ (2 * L)) : ℕ) : ℝ)) ^ tau) at hWitness
  obtain ⟨A, H, family, hHbound, hrate⟩ := hWitness
  obtain ⟨q, a, b, c, hrestrict, hpoint⟩ :=
    row211_pointwise_from_family
      (K := K) tau C₀ m L G A H
      (by simpa only [N] using family)
      (by simpa only [N] using hHbound)
      (by simpa only [N] using hrate)
  refine ⟨q, a, b, c, hrestrict, ?_⟩
  let raw : ℝ :=
    4 * (6 : ℝ) ^ (3 * tau) * ((6 : ℝ) ^ (3 * tau) + 2)
  let C : ℝ := 2 * C₀ + 400
  let x : ℝ := Real.sqrt (((N + 1 : ℕ) : ℝ))
  let y : ℝ := Real.sqrt
    (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))
  let R : ℕ := MME.DWZTable2Counts.component (14 : Fin 15) * m
  have hraw : 0 ≤ raw := by dsimp only [raw]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hNle : N + 1 ≤ MME.DWZTable2Counts.scale * m + 1 := by
    dsimp only [N, MME.DWZTable2Counts.scale]
    omega
  have hxy : x ≤ y := by
    dsimp only [x, y]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hNle)
  have hR : R = 2 * N := by
    change 2073445800000000 * m =
      2 * (1036722900000000 * m)
    ring
  have hpoint' : raw ^ (4 * N) * Real.exp (-C * x) ≤
      ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau) := by
    simpa only [raw, C, x, N] using hpoint
  exact rate_transport
    raw C x y (∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau))
    N R hraw hC hxy hR hpoint'

theorem witness_to_scaled_extraction
    {K : Type u} [Field K]
    (tau C₀ : ℝ) (hC₀ : 0 ≤ C₀) (m : ℕ)
    (hWitness : CapacityWitness tau C₀
      (1036722900000000 * m)) :
    ExtractionGoal K tau (2 * C₀ + 400) m := by
  dsimp only [ExtractionGoal]
  intro s hs
  rcases hs with rfl | rfl
  · exact row121_from_witness tau C₀ hC₀ m hWitness
  · exact row211_from_witness tau C₀ hC₀ m hWitness

theorem assemble_eventually
    {K : Type u} [Field K]
    (tau C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (hrate : ∀ᶠ N : ℕ in atTop, CapacityWitness tau C₀ N) :
    ∀ᶠ m : ℕ in atTop,
      ExtractionGoal K tau (2 * C₀ + 400) m := by
  let halfCount : ℕ := 1036722900000000
  rw [eventually_atTop] at hrate ⊢
  obtain ⟨N₀, hN₀⟩ := hrate
  refine ⟨N₀, ?_⟩
  intro m hm
  have hscaled : N₀ ≤ halfCount * m := by
    dsimp only [halfCount]
    omega
  exact witness_to_scaled_extraction
    tau C₀ hC₀ m (hN₀ (halfCount * m) hscaled)

theorem raw_extractions
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in atTop,
        ∀ s : Fin 15, (s = 13 ∨ s = 14) →
          ∃ (q : ℕ) (A B Cdim : Fin q → ℕ),
            TensorObj.Restrict
              (TensorObj.bigAdd (fun j ↦ MMObj K (A j) (B j) (Cdim j)))
              (sixSymmetrization (restrictedComponentPower K s m)) ∧
            (4 * (6 : ℝ) ^ (3 * tau) *
                ((6 : ℝ) ^ (3 * tau) + 2)) ^
                (2 * (MME.DWZTable2Counts.component s * m)) *
                Real.exp (-C * Real.sqrt
                  (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))) ≤
              ∑ j, (((A j * B j * Cdim j : ℕ) : ℝ) ^ tau) := by
  obtain ⟨C₀, hC₀, hcapacity⟩ :=
    mme_CW_q6_primary_hash_sqrt_capacity_bounded tau htau
  refine ⟨2 * C₀ + 400, by positivity, ?_⟩
  change ∀ᶠ m : ℕ in atTop,
    ExtractionGoal K tau (2 * C₀ + 400) m
  exact assemble_eventually tau C₀ hC₀ hcapacity

end P2M867

theorem solution
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in atTop,
        ∀ s : Fin 15, (s = 13 ∨ s = 14) →
          ∃ (q : ℕ) (A B Cdim : Fin q → ℕ),
            TensorObj.Restrict
              (TensorObj.bigAdd (fun j => MMObj K (A j) (B j) (Cdim j)))
              (sixSymmetrization (restrictedComponentPower K s m)) ∧
            (((componentBase tau s) ^
                (MME.DWZTable2Counts.component s * m)) ^ (6 : ℕ)) *
                Real.exp (-C * Real.sqrt
                  (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))) ≤
              ∑ j, (((A j * B j * Cdim j : ℕ) : ℝ) ^ tau) := by
  obtain ⟨C, hC, hextract⟩ := P2M867.raw_extractions (K := K) tau htau
  refine ⟨C, hC, ?_⟩
  filter_upwards [hextract] with m hm
  intro s hs
  obtain ⟨q, A, B, Cdim, hrestrict, hrate⟩ := hm s hs
  refine ⟨q, A, B, Cdim, hrestrict, ?_⟩
  let raw : ℝ :=
    4 * (6 : ℝ) ^ (3 * tau) * ((6 : ℝ) ^ (3 * tau) + 2)
  let R : ℕ := MME.DWZTable2Counts.component s * m
  have hcube : componentBase tau s ^ (3 : ℕ) = raw := by
    rcases hs with rfl | rfl
    · exact mme_dwz_q6_121_211_componentBase_cube tau
    · have h1314 : componentBase tau (13 : Fin 15) =
          componentBase tau (14 : Fin 15) := by
        norm_num [componentBase, Fin.ext_iff]
      rw [← h1314]
      exact mme_dwz_q6_121_211_componentBase_cube tau
  have hpower :
      ((componentBase tau s) ^ R) ^ (6 : ℕ) = raw ^ (2 * R) := by
    calc
      ((componentBase tau s) ^ R) ^ (6 : ℕ) =
          (componentBase tau s) ^ (R * 6) := by
            exact (pow_mul (componentBase tau s) R 6).symm
      _ = (componentBase tau s) ^ (3 * (2 * R)) := by
        congr 1
        omega
      _ = ((componentBase tau s) ^ (3 : ℕ)) ^ (2 * R) := by
        exact pow_mul (componentBase tau s) 3 (2 * R)
      _ = raw ^ (2 * R) := by rw [hcube]
  change ((componentBase tau s) ^ R) ^ (6 : ℕ) * _ ≤ _
  rw [hpower]
  simpa only [raw, R] using hrate
