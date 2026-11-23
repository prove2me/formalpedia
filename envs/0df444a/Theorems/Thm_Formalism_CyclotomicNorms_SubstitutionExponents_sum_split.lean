-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_SubstitutionExponents_sum_split
-- name    : Formalism.CyclotomicNorms.SubstitutionExponents.sum_split
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:55:55.108777+00:00
-- url     : https://prove2.me/theorems/7f644a97-0d4d-4023-9e3f-8776fec9ee12
-- title:
--   Substitution Exponents: sum split
-- statement:
--   The Substitution Exponents construction uses the sum split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/SubstitutionBound.lean#L51-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/SubstitutionBound.lean#L51-L58

import Definitions.Def_Formalism_CyclotomicNorms_StatementA
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_SubstitutionBound
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
open Formalism.CyclotomicNorms.SubstitutionExponents
variable {r : ℕ}

theorem Formalism.CyclotomicNorms.SubstitutionExponents.sum_split (g : Fin r → ℕ) (j : Fin r) :
    ∑ i, g i = ∑ i ∈ univ.filter (· < j), g i + g j + ∑ i ∈ univ.filter (j < ·), g i := by sorry
