-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_glAct_wtspC
-- name    : Formalism.InvariantFactorPaths.L4.glAct_wtspC
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:40:36.975898+00:00
-- url     : https://prove2.me/theorems/1ea62322-6a91-4884-9d8d-fff2f17dda6d
-- title:
--   L4: gl Act wtsp C
-- statement:
--   The L4 construction uses the gl Act wtsp C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/FirstWeightLeOfSupport.lean#L123-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/FirstWeightLeOfSupport.lean#L123-L137

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

theorem Formalism.InvariantFactorPaths.L4.glAct_wtspC (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (c d : Fin r) (μ : Fin r → ℤ) :
    ∀ x ∈ WtSpC p LL j Cs μ, glAct p LL j c d x ∈ WtSpC p LL j Cs (shiftW μ c d) := by sorry
