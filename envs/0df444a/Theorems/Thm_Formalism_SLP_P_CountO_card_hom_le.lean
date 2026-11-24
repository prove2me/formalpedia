-- Prove2me | Theorems.Thm_Formalism_SLP_P_CountO_card_hom_le
-- name    : Formalism.SLP.P.CountO.card_hom_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:28:56.919203+00:00
-- url     : https://prove2.me/theorems/11c4f6f4-e598-463c-8ed4-7eeb51bd7f45
-- title:
--   Count O: card hom le
-- statement:
--   The Count O construction uses the card hom le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HyperbolicPlaceProducts/SubgroupIndexCounts/CountO.lean#L139-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HyperbolicPlaceProducts/SubgroupIndexCounts/CountO.lean#L139-L163

import Definitions.Def_Formalism_HyperbolicPlaceProducts_Statement
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_CountO
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.SLP Formalism.SLP.P
open Formalism.SLP.P.CountO
variable {R : Type} [CommRing R] [IsDedekindDomain R]

theorem Formalism.SLP.P.CountO.card_hom_le (P : Ideal R) [P.IsMaximal] [Finite (R ⧸ P)] {X : Type}
    [AddCommGroup X] [Module R X] (k : ℕ) (s : Finset X) (hsk : s.card ≤ k)
    (hs : Submodule.span R (s : Set X) ⊔ P • ⊤ = ⊤) :
    Finite (X →ₗ[R] R ⧸ P) ∧ Nat.card (X →ₗ[R] R ⧸ P) ≤ Nat.card (R ⧸ P) ^ k := by sorry
