-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_glRest_comm
-- name    : Formalism.InvariantFactorPaths.L4.glRest_comm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:43:23.062504+00:00
-- url     : https://prove2.me/theorems/0c3c770b-5dd5-43f0-8860-0f0909274ccf
-- title:
--   L4: gl Rest comm
-- statement:
--   The L4 construction uses the gl Rest comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/FirstWeightLeOfSupport.lean#L470-L476
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/FirstWeightLeOfSupport.lean#L470-L476

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

theorem Formalism.InvariantFactorPaths.L4.glRest_comm (LL : Letters N) (j j' : ℕ) (hjj : j ≤ j') (c d a b : Fin r)
    (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    glRest p LL j j' c d (glAct p LL j a b x) = glAct p LL j a b (glRest p LL j j' c d x) := by sorry
