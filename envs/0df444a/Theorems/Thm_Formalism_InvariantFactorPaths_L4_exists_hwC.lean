-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_exists_hwC
-- name    : Formalism.InvariantFactorPaths.L4.exists_hwC
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:43:07.484798+00:00
-- url     : https://prove2.me/theorems/94119cc6-bc1b-4f3a-98d4-cc7b431d9407
-- title:
--   L4: exists hw C
-- statement:
--   The L4 construction uses the exists hw C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/FirstWeightLeOfSupport.lean#L202-L281
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/FirstWeightLeOfSupport.lean#L202-L281

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_InitPartZeroXMul
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FirstWeightLeOfSupport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem Formalism.InvariantFactorPaths.L4.exists_hwC (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r))
    (S : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))
    (hSP : S ≤ Pol p r LL) (hS : ∀ c ∈ Cs, ∀ d ∈ Cs, ∀ x ∈ S, glAct p LL j c d x ∈ S)
    (x : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hx : x ∈ S) (hx0 : x ≠ 0) : ∃ h ∈ S, h ≠ 0 ∧ ∃ μ, h ∈ HWC p LL j Cs μ := by sorry
