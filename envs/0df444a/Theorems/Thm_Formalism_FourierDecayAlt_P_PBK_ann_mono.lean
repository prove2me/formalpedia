-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_ann_mono
-- name    : Formalism.FourierDecayAlt.P.PBK.ann_mono
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:16:42.873586+00:00
-- url     : https://prove2.me/theorems/a663a512-47bf-4e13-88dd-6771e7efc2df
-- title:
--   PBK: ann mono
-- statement:
--   The PBK construction uses the ann mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ZeroNotMemPreimagePow.lean#L29-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ZeroNotMemPreimagePow.lean#L29-L33

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AestronglyMeasurableMainD
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralNormCvecSq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermFibreKernels
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ZeroNotMemPreimagePow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBK
open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace
noncomputable section
open Classical

theorem Formalism.FourierDecayAlt.P.PBK.ann_mono : Monotone ann := by sorry
