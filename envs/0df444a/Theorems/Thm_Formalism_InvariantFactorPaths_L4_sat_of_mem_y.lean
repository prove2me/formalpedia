-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_sat_of_mem_y
-- name    : Formalism.InvariantFactorPaths.L4.sat_of_mem_y
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:12:46.051557+00:00
-- url     : https://prove2.me/theorems/e81831a2-eca4-4d4e-af08-1821a3be51fe
-- title:
--   L4: sat of mem y
-- statement:
--   The L4 construction uses the sat of mem y property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/RestrictedSaturationHolds.lean#L13-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/RestrictedSaturationHolds.lean#L13-L27

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_DerivativeKillsDegreeZero
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RestrictedLatticeDividedPower
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_WmMulWmComm
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_DerivativeDividedIntegral
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RestrictedSaturationHolds
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

theorem Formalism.InvariantFactorPaths.L4.sat_of_mem_y {r : ℕ} [NeZero r] (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
    (ρ : Fin r) (n : ℕ) (x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (hF : x ∈ FreeOf p (Fin.last K, ρ))
    (hY : x ∈ Y p LL J M) (hi : x ∈ IntPol p (Fin (K + 1) × Fin r)) :
    ∃ h ∈ Y p LL J M, h ∈ IntPol p (Fin (K + 1) × Fin r) ∧
      initPart (Fin.last K, ρ) 0 h = ((p : ℚ_[p]) ^ n) • x := by sorry
