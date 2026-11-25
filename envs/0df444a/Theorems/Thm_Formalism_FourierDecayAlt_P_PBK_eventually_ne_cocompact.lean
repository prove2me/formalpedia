-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_eventually_ne_cocompact
-- name    : Formalism.FourierDecayAlt.P.PBK.eventually_ne_cocompact
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T06:00:36.882728+00:00
-- url     : https://prove2.me/theorems/1cc77075-5af5-4e1c-bd2a-c4f3e49e2c56
-- title:
--   PBK: eventually ne cocompact
-- statement:
--   The PBK construction uses the eventually ne cocompact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GermFibreKernels.lean#L26-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GermFibreKernels.lean#L26-L28

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermRealisation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermFibreKernels
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
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem Formalism.FourierDecayAlt.P.PBK.eventually_ne_cocompact (c : ℂ) : ∀ᶠ x in cocompact ℂ, x ≠ c := by sorry
