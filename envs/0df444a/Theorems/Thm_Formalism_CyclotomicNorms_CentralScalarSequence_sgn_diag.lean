-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_CentralScalarSequence_sgn_diag
-- name    : Formalism.CyclotomicNorms.CentralScalarSequence.sgn_diag
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:53:54.347918+00:00
-- url     : https://prove2.me/theorems/cecdf98c-0c09-4511-a716-3edfe7ec4eca
-- title:
--   Central Scalar Sequence: sgn diag
-- statement:
--   The Central Scalar Sequence construction uses the sgn diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/Central.lean#L116-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/Central.lean#L116-L117

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
variable {R W : Type} [CommRing R] [AddCommGroup W] [Module R W]

theorem Formalism.CyclotomicNorms.CentralScalarSequence.sgn_diag (i : ℕ) : (-1 : R) ^ (i + (i + 1)) = -1 := by sorry
