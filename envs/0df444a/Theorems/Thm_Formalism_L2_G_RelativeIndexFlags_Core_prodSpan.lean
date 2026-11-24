-- Prove2me | Theorems.Thm_Formalism_L2_G_RelativeIndexFlags_Core_prodSpan
-- name    : Formalism.L2.G.RelativeIndexFlags.Core.prodSpan
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:34:56.235327+00:00
-- url     : https://prove2.me/theorems/0a7d2d09-c0ec-46a8-a00a-774ba2dfb9b2
-- title:
--   Core: prod Span
-- statement:
--   The Core construction uses the prod Span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/IntegralWeylLatticeSpan/WeylEqSpanInt.lean#L11-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/IntegralWeylLatticeSpan/WeylEqSpanInt.lean#L11-L15

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Lemmata_GeneralBFactLeftSide_Imports
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_IntegralWeylLatticeSpan_WeylEqSpanInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix Formalism.GradedWeylDivisibility
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.RelativeIndexFlags Formalism.L2.G.RelativeIndexFlags.Core

theorem Formalism.L2.G.RelativeIndexFlags.Core.prodSpan {O A I : Type} [CommRing O] [CommRing A] [Algebra O A] [Fintype I] [DecidableEq I]
    {B : I → Type} [∀ i, AddCommGroup (B i)] [∀ i, Module O (B i)] (ε : ∀ i, B i →ₗ[O] A) (T : ∀ i, Set (B i)) :
    Submodule.span O {X | ∃ F : ∀ i, B i, (∀ i, F i ∈ Submodule.span O (T i)) ∧ X = ∏ i, ε i (F i)} =
      Submodule.span O {X | ∃ F : ∀ i, B i, (∀ i, F i ∈ T i) ∧ X = ∏ i, ε i (F i)} := by sorry
