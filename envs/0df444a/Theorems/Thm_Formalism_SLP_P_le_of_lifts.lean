-- Prove2me | Theorems.Thm_Formalism_SLP_P_le_of_lifts
-- name    : Formalism.SLP.P.le_of_lifts
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:29:00.699534+00:00
-- url     : https://prove2.me/theorems/f88866a2-cc84-4766-8890-3b106432878b
-- title:
--   P: le of lifts
-- statement:
--   The P construction uses the le of lifts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HyperbolicPlaceProducts/SubgroupIndexCounts/SubgroupCount.lean#L31-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HyperbolicPlaceProducts/SubgroupIndexCounts/SubgroupCount.lean#L31-L56

import Definitions.Def_Formalism_HyperbolicPlaceProducts_Statement
import Mathlib
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_SubgroupCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.SLP Formalism.SLP.P
open AddSubgroup

theorem Formalism.SLP.P.le_of_lifts {A : Type*} [AddCommGroup A] {H₁ H₂ : AddSubgroup (ℤ × A)} {ι : Type*}
    (v : ι → A) (hv : AddSubgroup.closure (Set.range v) = H₁.map (AddMonoidHom.snd ℤ A))
    (hk : H₁.comap (AddMonoidHom.inl ℤ A) ≤ H₂.comap (AddMonoidHom.inl ℤ A))
    (hlift : ∀ i, ∃ x : ℤ, (x, v i) ∈ H₁ ⊓ H₂) : H₁ ≤ H₂ := by sorry
