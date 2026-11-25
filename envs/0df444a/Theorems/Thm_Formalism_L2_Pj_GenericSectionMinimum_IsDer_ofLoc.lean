-- Prove2me | Theorems.Thm_Formalism_L2_Pj_GenericSectionMinimum_IsDer_ofLoc
-- name    : Formalism.L2.Pj.GenericSectionMinimum.IsDer.ofLoc
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:32:09.302294+00:00
-- url     : https://prove2.me/theorems/e27c72c5-2fc5-4dad-884b-9d49344e4bbb
-- title:
--   Is Der: of Loc
-- statement:
--   The Is Der construction uses the of Loc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/PowMapMemOfPowMulMem.lean#L134-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/PowMapMemOfPowMulMem.lean#L134-L182

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PowMapMemOfPowMulMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.GenericSectionMinimum
open Formalism.L2.Pj.GenericSectionMinimum.IsDer
variable {A : Type*} [CommRing A] {δ : A → A}

theorem Formalism.L2.Pj.GenericSectionMinimum.IsDer.ofLoc {B : Type*} [CommRing B] [Algebra A B] (S : Submonoid A) [IsLocalization S B] (d : A → B)
    (hadd : ∀ x y, d (x + y) = d x + d y)
    (hmul : ∀ x y, d (x * y) = algebraMap A B x * d y + algebraMap A B y * d x) :
    ∃ δ' : B → B, IsDer δ' ∧ ∀ a, δ' (algebraMap A B a) = d a := by sorry
