-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_GermFibreKernels_PKer_fm_inner_add
-- name    : Formalism.FourierDecayAlt.P.GermFibreKernels.PKer.fm_inner_add
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:25:45.159512+00:00
-- url     : https://prove2.me/theorems/bdfb7ebf-79f3-4871-944b-c4344a6ddd87
-- title:
--   PKer: fm inner add
-- statement:
--   The PKer construction uses the fm inner add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FmSmulLeft.lean#L33-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FmSmulLeft.lean#L33-L35

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

theorem Formalism.FourierDecayAlt.P.GermFibreKernels.PKer.fm_inner_add (x : α) (g₁ g₂ : α →₀ ℂ) :
    ((g₁ + g₂).sum fun y b => P.K x y * b) = (g₁.sum fun y b => P.K x y * b) + g₂.sum fun y b => P.K x y * b := by sorry
