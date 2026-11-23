-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A6x4_addChar_ne_zero
-- name    : Formalism.FourierDecayAlt.P.A6x4.addChar_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:50:17.239077+00:00
-- url     : https://prove2.me/theorems/c5350918-547a-4de4-adc9-603aaac3e1b7
-- title:
--   A6x4: add Char ne zero
-- statement:
--   The A6x4 construction uses the add Char ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ModulusLocallyConstant.lean#L68-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ModulusLocallyConstant.lean#L68-L72

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModulusLocallyConstant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A6x4
variable {K : Type} [CommRing K]

theorem Formalism.FourierDecayAlt.P.A6x4.addChar_ne_zero {G : Type} [AddGroup G] (φ : AddChar G ℂ) (x : G) : φ x ≠ 0 := by sorry
