-- Prove2me | Theorems.Thm_Formalism_L2_Pj_GenericSectionMinimum_IsDer_der_sum
-- name    : Formalism.L2.Pj.GenericSectionMinimum.IsDer.der_sum
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:32:15.996609+00:00
-- url     : https://prove2.me/theorems/4ca3a969-3ef3-4614-b60f-ae91facf526d
-- title:
--   Is Der: der sum
-- statement:
--   The Is Der construction uses the der sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/PowMapMemOfPowMulMem.lean#L51-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/PowMapMemOfPowMulMem.lean#L51-L52

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

theorem Formalism.L2.Pj.GenericSectionMinimum.IsDer.der_sum (h : IsDer δ) {ι : Type*} (s : Finset ι) (f : ι → A) : δ (∑ i ∈ s, f i) = ∑ i ∈ s, δ (f i) := by sorry
