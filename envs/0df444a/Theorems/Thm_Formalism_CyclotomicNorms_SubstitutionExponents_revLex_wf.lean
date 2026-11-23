-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_SubstitutionExponents_revLex_wf
-- name    : Formalism.CyclotomicNorms.SubstitutionExponents.revLex_wf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:55:49.645337+00:00
-- url     : https://prove2.me/theorems/741be63b-14be-48ae-a9eb-a2df9732e6cf
-- title:
--   Substitution Exponents: rev Lex wf
-- statement:
--   The Substitution Exponents construction uses the rev Lex wf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/SubstitutionBound.lean#L48-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/SubstitutionBound.lean#L48-L49

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

theorem Formalism.CyclotomicNorms.SubstitutionExponents.revLex_wf : WellFounded (revLex (r := r)) := by sorry
