-- Prove2me | solution 1 for mme_stothers_phi125_profile_cofinal_finite_extraction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-03T00:11:56.802478+00:00
-- url     : https://prove2.me/submissions/15cbd6ef-15df-4ba6-b45f-02b22937d312

import Theorems.Thm_mme_stothers_phi125_finite_power_block_certificate
import Theorems.Thm_mme_HasTauValueAtLeast_bigAdd_uniform_strict
import Theorems.Thm_mme_HasTauValueAtLeast_mono_restrict
import Theorems.Thm_mme_HasTauValueAtLeast_kronPow_root
import Theorems.Thm_mme_HasTauValueAtLeast_to_cofinal_finite_extractions

open MME BigOperators Filter

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K] (tau a b : ℝ)
    (htauLower : 2 ≤ 3 * tau) (htauUpper : 3 * tau ≤ 3)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b ≤ 1)
    (V : ℝ) (hV : 0 ≤ V)
    (hVlt :
      V <
        4 / MME.StothersFourth.H 6 tau *
          ((MME.StothersFourth.L 6 tau / a) ^ a *
            ((MME.StothersFourth.E 6 tau *
              MME.StothersFourth.H 6 tau) / (1 - a)) ^ (1 - a)) *
          ((MME.StothersFourth.L 6 tau / b) ^ b *
            ((2 * MME.StothersFourth.H 6 tau) / (1 - b)) ^
              (1 - b))) :
    ∃ (s : ℕ → ℕ) (loss : ℕ → ℝ),
      Tendsto s atTop atTop ∧
      Tendsto loss atTop (nhds 0) ∧
      ∀ᶠ n : ℕ in atTop,
        ∃ (k : ℕ) (x y z : Fin k → ℕ),
          TensorObj.Restrict
            (TensorObj.bigAdd (fun i ↦ MMObj K (x i) (y i) (z i)))
            ((cyclicSymmetrization
              (MME.StothersFourth.cwFourthConstituent K 6 1 2 5)).kronPow
                (s n)) ∧
          V ^ (s n) * (1 - loss n) ≤
            ∑ i, (((x i * y i * z i : ℕ) : ℝ) ^ tau) := by
  obtain ⟨N, alpha, beta, gamma, hN, hsum, kept, block, B,
      _hmode, hrestrict, hB, hblock, hrate⟩ :=
    mme_stothers_phi125_finite_power_block_certificate
      (K := K) tau a b htauLower htauUpper ha hb hab V hV hVlt
  let F : Fin kept.card → TensorObj K 3 :=
    fun j ↦ block (kept.equivFin.symm j)
  have hsumValue :
      HasTauValueAtLeast (TensorObj.bigAdd F) tau (V ^ (2 * N)) := by
    apply mme_HasTauValueAtLeast_bigAdd_uniform_strict
      F tau B hB
    · intro j W hW hWB
      exact hblock (kept.equivFin.symm j) W hW hWB
    · exact pow_nonneg hV _
    · simpa only [F] using hrate
  have hpower :
      HasTauValueAtLeast
        ((cyclicSymmetrization
          (MME.StothersFourth.cwFourthConstituent K 6 1 2 5)).kronPow
            (2 * N)) tau (V ^ (2 * N)) :=
    mme_HasTauValueAtLeast_mono_restrict
      (by simpa only [F] using hrestrict) hsumValue
  have htwoN : 0 < 2 * N := Nat.mul_pos (by norm_num) hN
  have hsource :
      HasTauValueAtLeast
        (cyclicSymmetrization
          (MME.StothersFourth.cwFourthConstituent K 6 1 2 5)) tau V :=
    mme_HasTauValueAtLeast_kronPow_root
      (cyclicSymmetrization
        (MME.StothersFourth.cwFourthConstituent K 6 1 2 5))
      tau V (2 * N) htwoN hV hpower
  obtain ⟨s, loss, hs, hloss, _hlossPos, hextract⟩ :=
    mme_HasTauValueAtLeast_to_cofinal_finite_extractions
      (cyclicSymmetrization
        (MME.StothersFourth.cwFourthConstituent K 6 1 2 5))
      tau V hsource
  exact ⟨s, loss, hs, hloss, Filter.Eventually.of_forall hextract⟩
