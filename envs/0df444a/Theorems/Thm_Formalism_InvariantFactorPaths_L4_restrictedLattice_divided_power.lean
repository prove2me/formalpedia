-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_restrictedLattice_divided_power
-- name    : Formalism.InvariantFactorPaths.L4.restrictedLattice_divided_power
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:54:24.632427+00:00
-- url     : https://prove2.me/theorems/b9f1a284-b39f-44e0-ba0d-006451b2d58c
-- title:
--   L4: restricted Lattice divided power
-- statement:
--   The L4 construction uses the restricted Lattice divided power property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/RestrictedLatticeDividedPower.lean#L52-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/RestrictedLatticeDividedPower.lean#L52-L72

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_LatDefs
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_MulEarlyModP
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_DischargeHeightBound
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RestrictedLatticeDividedPower
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.GM.DimensionMonotonicity Formalism.CountingSumsFrames Formalism.InvariantFactorPaths.PW MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {K : ℕ}
variable {r : ℕ} [NeZero r]

theorem Formalism.InvariantFactorPaths.L4.restrictedLattice_divided_power (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r)
    (A B : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (k : ℕ)
    (hAB : ∀ x, resL p (Fin.last K, ρ) 0 (A x) = B (resL p (Fin.last K, ρ) 0 x))
    (hint : ∀ x ∈ IntPol p (Fin (K + 1) × Fin r),
      ((k.factorial : ℚ_[p]))⁻¹ • (A ^ k) x ∈ IntPol p (Fin (K + 1) × Fin r))
    (hY : ∀ o : ℕ, ∀ h ∈ Y p (setLast LL o) J M, ∃ o' : ℕ, (A ^ k) h ∈ Y p (setLast LL o') J M) :
    ∀ z ∈ M2 p LL J M ρ, ((k.factorial : ℚ_[p]))⁻¹ • (B ^ k) z ∈ M2 p LL J M ρ := by sorry
