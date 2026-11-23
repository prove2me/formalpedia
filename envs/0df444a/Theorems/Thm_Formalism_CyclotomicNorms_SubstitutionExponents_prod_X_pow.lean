-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_SubstitutionExponents_prod_X_pow
-- name    : Formalism.CyclotomicNorms.SubstitutionExponents.prod_X_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:56:03.180094+00:00
-- url     : https://prove2.me/theorems/a354c648-8e53-49df-9274-506a18f83de1
-- title:
--   Substitution Exponents: prod X pow
-- statement:
--   The Substitution Exponents construction uses the prod X pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/SubstitutionBound.lean#L15-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/SubstitutionBound.lean#L15-L21

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

theorem Formalism.CyclotomicNorms.SubstitutionExponents.prod_X_pow {k : Type*} [CommRing k] (n : Fin r → ℕ) (d : Fin r →₀ ℕ) :
    (d.prod fun s e => ((PowerSeries.X : PowerSeries k) ^ n s) ^ e) =
      PowerSeries.X ^ weight n d := by sorry
