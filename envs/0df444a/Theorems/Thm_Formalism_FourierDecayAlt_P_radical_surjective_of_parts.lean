-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_radical_surjective_of_parts
-- name    : Formalism.FourierDecayAlt.P.radical_surjective_of_parts
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T02:14:42.742277+00:00
-- url     : https://prove2.me/theorems/61a42205-0adf-4767-b4b1-e05f73d4f78f
-- title:
--   P: radical surjective of parts
-- statement:
--   The P construction uses the radical surjective of parts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NFRadRedS.lean#L261-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NFRadRedS.lean#L261-L262

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NFRadRedA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NFRadRedS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P

theorem Formalism.FourierDecayAlt.P.radical_surjective_of_parts : NFRadRedS.LocSec → NFRadRedS.RepSmooth → Formalism.FourierDecayAlt.NF.RadRedSurj := by sorry
