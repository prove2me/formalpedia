-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_SubstitutionExponents_unique_of_min
-- name    : Formalism.CyclotomicNorms.SubstitutionExponents.unique_of_min
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:56:19.64389+00:00
-- url     : https://prove2.me/theorems/ac4c50ed-61d9-4d8a-aecf-3219139ba022
-- title:
--   Substitution Exponents: unique of min
-- statement:
--   The Substitution Exponents construction uses the unique of min property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/SubstitutionBound.lean#L60-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/SubstitutionBound.lean#L60-L94

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

theorem Formalism.CyclotomicNorms.SubstitutionExponents.unique_of_min (n : Fin r → ℕ) (a : Fin r →₀ ℕ)
    (hn : ∀ j, ∑ i ∈ univ.filter (· < j), a i * n i < n j)
    (d : Fin r →₀ ℕ) (hmin : ¬ revLex d a) (hw : weight n d = weight n a) : d = a := by sorry
