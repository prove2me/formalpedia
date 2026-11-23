-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_SubstitutionExponents_coeff_subst_weight
-- name    : Formalism.CyclotomicNorms.SubstitutionExponents.coeff_subst_weight
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:55:54.733168+00:00
-- url     : https://prove2.me/theorems/8d273c9d-15cd-4b5d-af88-67f365791764
-- title:
--   Substitution Exponents: coeff subst weight
-- statement:
--   The Substitution Exponents construction uses the coeff subst weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/SubstitutionBound.lean#L31-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/SubstitutionBound.lean#L31-L43

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

theorem Formalism.CyclotomicNorms.SubstitutionExponents.coeff_subst_weight {k : Type*} [CommRing k] (n : Fin r → ℕ) (hn : ∀ j, n j ≠ 0)
    (F : MvPowerSeries (Fin r) k) (m : ℕ) :
    PowerSeries.coeff m
        (MvPowerSeries.subst (fun j => (PowerSeries.X : PowerSeries k) ^ n j) F : PowerSeries k) =
      finsum (fun d => if weight n d = m then MvPowerSeries.coeff d F else 0) := by sorry
