-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LocalVolumePositivity_pos_idx
-- name    : Formalism.FourierDecayAlt.P.LocalVolumePositivity.pos_idx
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:53:54.655275+00:00
-- url     : https://prove2.me/theorems/f4564b43-5928-4c68-8b6a-193455722402
-- title:
--   Local Volume Positivity: pos idx
-- statement:
--   The Local Volume Positivity construction uses the pos idx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LocalVolumePositivity.lean#L61-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LocalVolumePositivity.lean#L61-L63

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalVolumePositivity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Formalism.FourierDecayAlt.S3
open Formalism.FourierDecayAlt.P.LocalVolumePositivity
variable {P : Type} [Fintype P] {B : MassData P}

theorem Formalism.FourierDecayAlt.P.LocalVolumePositivity.pos_idx (hP : B.Pos) : 0 < ∏ p, B.gg p / (B.nn p * B.uk p) := by sorry
