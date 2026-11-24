-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_fr_residue_form
-- name    : Formalism.FourierDecayAlt.P.fr_residue_form
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:50:45.624908+00:00
-- url     : https://prove2.me/theorems/2747ff0e-262e-4738-a24b-4475c30f1ee4
-- title:
--   P: fr residue form
-- statement:
--   The P construction uses the fr residue form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ResidueForm.lean#L237-L302
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ResidueForm.lean#L237-L302

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ResidueForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Matrix Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.P.Fr11

theorem Formalism.FourierDecayAlt.P.fr_residue_form : Formalism.FourierDecayAlt.Fr.ResidueForm := by sorry
