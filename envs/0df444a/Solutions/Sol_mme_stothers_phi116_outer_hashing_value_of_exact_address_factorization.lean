-- Prove2me | solution 1 for mme_stothers_phi116_outer_hashing_value_of_exact_address_factorization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T20:40:41.163078+00:00
-- url     : https://prove2.me/submissions/10394982-45b3-4035-ac3a-6a0ce7f04b8d

import Theorems.Thm_mme_stothers_phi116_optimal_profile_rate
import Theorems.Thm_mme_stothers_phi116_profile_extraction_of_exact_address_factorization

open MME

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K] (tau : Real)
    (htauLower : 2 ≤ 3 * tau) (htauUpper : 3 * tau ≤ 3)
    (hfactor :
      ∀ {N alpha beta : ℕ}, alpha + beta = N →
        ∀ address : CWQ6ExactCoupledAddress N alpha beta,
          TensorObj.Restrict
            (TensorObj.kronFin 4 (fun r ↦
              (MME.StothersFourth.Phi116.phi116ComponentObj K r).kronPow
                (MME.StothersFourth.Phi116.phi116ComponentMultiplicity
                  alpha beta r)))
            (gradedAddressBlock
              (MME.StothersFourth.Phi116.cwPhi116ThreeGrading K)
              address.1)) :
    ∀ V : Real, 0 ≤ V →
      V < MME.StothersFourth.classValue 6 tau 5 →
      HasTauValueAtLeast
        (cyclicSymmetrization
          (MME.StothersFourth.cwFourthConstituent K 6 1 1 6)) tau V := by
  have hE : 0 < MME.StothersFourth.E 6 tau := by
    unfold MME.StothersFourth.E
    positivity
  have hL : 0 < MME.StothersFourth.L 6 tau := by
    unfold MME.StothersFourth.L
    positivity
  let a :=
    (2 * MME.StothersFourth.L 6 tau) /
      (2 * MME.StothersFourth.L 6 tau +
        MME.StothersFourth.E 6 tau ^ (2 : ℕ))
  have hopt := mme_stothers_phi116_optimal_profile_rate
    (MME.StothersFourth.E 6 tau) (MME.StothersFourth.L 6 tau) hE hL
  change 0 < a ∧ a < 1 ∧
      4 *
          (((2 * MME.StothersFourth.L 6 tau) / a) ^ a *
            ((MME.StothersFourth.E 6 tau ^ (2 : ℕ)) / (1 - a)) ^
              (1 - a)) =
        4 *
          (MME.StothersFourth.E 6 tau ^ (2 : ℕ) +
            2 * MME.StothersFourth.L 6 tau) at hopt
  rcases hopt with ⟨haPos, haLt, hrate⟩
  intro V hV hVlt
  apply mme_stothers_phi116_profile_extraction_of_exact_address_factorization
    tau a htauLower htauUpper haPos haLt hfactor V hV
  calc
    V < MME.StothersFourth.classValue 6 tau 5 := hVlt
    _ = 4 *
          (MME.StothersFourth.E 6 tau ^ (2 : ℕ) +
            2 * MME.StothersFourth.L 6 tau) := rfl
    _ = 4 *
          (((2 * MME.StothersFourth.L 6 tau) / a) ^ a *
            ((MME.StothersFourth.E 6 tau ^ (2 : ℕ)) / (1 - a)) ^
              (1 - a)) := hrate.symm
