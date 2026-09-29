-- Prove2me | solution 1 for mme_CW_q6_primary_hash_Ctensor_outer_middle_certificates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T04:34:14.499168+00:00
-- url     : https://prove2.me/submissions/02295bce-69ca-4857-ba16-f2814843529f

import Mathlib.Analysis.SpecialFunctions.Exp
import Theorems.Thm_mme_CW_q6_primary_hash_induced_family_exists
import Theorems.Thm_mme_CW_q6_primary_hash_family_Ctensor_certificates

open MME Filter Topology

universe u

theorem solution
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∀ᶠ N : ℕ in atTop,
      let lambda : ℝ := 2 / ((6 : ℝ) ^ (3 * tau) + 2)
      let L : ℕ := ⌊lambda * (N : ℝ)⌋₊
      let Gcount : ℕ := N - L
      let Zcount : ℕ :=
        Nat.choose (2 * N) L * Nat.choose (2 * N - L) L
      let Xcount : ℕ := Nat.choose N Gcount
      let middle : ℕ := Nat.choose (2 * Gcount) Gcount
      let loss : ℝ :=
        (Real.sqrt (Real.sqrt (((N + 1 : ℕ) : ℝ))))⁻¹
      (0 < L ∧ L + Gcount = N ∧ 341 * L < 100 * Gcount) →
      ∃ A H : ℕ,
        0 < H ∧
        H ≤ 4 ^ N ∧
        Nonempty
          (CTensorOneHOneFamilyCertificate
            ((coupledObj K 6).kronPow (2 * N))
            A H (6 ^ (4 * Gcount + 2 * L))) ∧
        (Zcount : ℝ) * Real.exp (-((N : ℝ) * loss / 12)) ≤
          (A : ℝ) ∧
        (middle : ℝ) * Real.exp (-((N : ℝ) * loss / 8)) ≤
          4 * (Xcount : ℝ) ^ 2 * (H : ℝ) := by
  have hfamilies :=
    mme_CW_q6_primary_hash_induced_family_exists tau htau
  filter_upwards [hfamilies] with N hN
  dsimp only at hN ⊢
  intro hprofile
  obtain ⟨A, H, family, hHle, hA, hmiddle⟩ := hN hprofile
  refine ⟨A, H, family.hHpos, hHle, ?_, hA, hmiddle⟩
  exact mme_CW_q6_primary_hash_family_Ctensor_certificates
    (K := K) N
      ⌊2 / ((6 : ℝ) ^ (3 * tau) + 2) * (N : ℝ)⌋₊
      (N - ⌊2 / ((6 : ℝ) ^ (3 * tau) + 2) * (N : ℝ)⌋₊)
      A H family
