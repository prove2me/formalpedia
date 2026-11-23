-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_CentralScalarSequence_contr_agree
-- name    : Formalism.CyclotomicNorms.CentralScalarSequence.contr_agree
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:53:57.283839+00:00
-- url     : https://prove2.me/theorems/380ea0c3-4404-4a43-b08d-b2f17f61b3cc
-- title:
--   Central Scalar Sequence: contr agree
-- statement:
--   The Central Scalar Sequence construction uses the contr agree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/Central.lean#L37-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/Central.lean#L37-L41

import Definitions.Def_Formalism_CyclotomicNorms_StatementA
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_Central
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.CyclotomicNorms
open Formalism.CyclotomicNorms.CentralScalarSequence
variable {G : Type} [Group G]

theorem Formalism.CyclotomicNorms.CentralScalarSequence.contr_agree {m : ℕ} (j : Fin (m + 1)) (x : Fin (m + 1) → G) (y : ℕ → G)
    (hx : ∀ k : Fin (m + 1), x k = y k) :
    ∀ k : Fin m, Fin.contractNth j (· * ·) x k = contrN j y k := by sorry
