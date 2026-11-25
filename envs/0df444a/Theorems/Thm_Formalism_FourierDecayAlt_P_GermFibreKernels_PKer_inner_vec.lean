-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_GermFibreKernels_PKer_inner_vec
-- name    : Formalism.FourierDecayAlt.P.GermFibreKernels.PKer.inner_vec
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T02:53:04.760474+00:00
-- url     : https://prove2.me/theorems/994e56c8-da16-583a-bec4-b9389e6dc4d1
-- title:
--   PKer: inner vec
-- statement:
--   The PKer construction uses the inner vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FmSmulLeft.lean#L83-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FmSmulLeft.lean#L83-L88

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementTB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FmSmulLeft
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GermFibreKernels
open scoped InnerProductSpace ComplexConjugate ComplexOrder
noncomputable section
open Formalism.FourierDecayAlt.P.GermFibreKernels.PKer
variable {α : Type} (P : PKer α)

theorem Formalism.FourierDecayAlt.P.GermFibreKernels.PKer.inner_vec (x y : α) : ⟪P.vec x, P.vec y⟫_ℂ = P.K x y := by sorry
