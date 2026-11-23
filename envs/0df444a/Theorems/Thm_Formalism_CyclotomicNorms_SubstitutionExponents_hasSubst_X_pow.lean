-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_SubstitutionExponents_hasSubst_X_pow
-- name    : Formalism.CyclotomicNorms.SubstitutionExponents.hasSubst_X_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:56:03.851382+00:00
-- url     : https://prove2.me/theorems/d7418fd9-75a5-49bb-9ed7-3f3363c6db31
-- title:
--   Substitution Exponents: has Subst X pow
-- statement:
--   The Substitution Exponents construction uses the has Subst X pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/SubstitutionBound.lean#L23-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/SubstitutionBound.lean#L23-L29

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

theorem Formalism.CyclotomicNorms.SubstitutionExponents.hasSubst_X_pow {k : Type*} [CommRing k] (n : Fin r → ℕ) (hn : ∀ j, n j ≠ 0) :
    MvPowerSeries.HasSubst (fun j => (PowerSeries.X : PowerSeries k) ^ n j) := by sorry
