-- Prove2me | Theorems.Thm_Formalism_DivisionValues_ConjugateWeightGram_exists_reduced
-- name    : Formalism.DivisionValues.ConjugateWeightGram.exists_reduced
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:12:02.828827+00:00
-- url     : https://prove2.me/theorems/36a3a789-9b7c-4c0e-b72d-ab290eee8580
-- title:
--   Conjugate Weight Gram: exists reduced
-- statement:
--   The Conjugate Weight Gram construction uses the exists reduced property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ConjugateWeightLatticeOfGeneral.lean#L574-L631
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ConjugateWeightLatticeOfGeneral.lean#L574-L631

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_RatHermLcvTwist
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DivIntoDual
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_BoundsChain
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_JwConj
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DualMu
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
open RationalHermitianForm
open Formalism.DivisionValues.ConjugateWeightGram

theorem Formalism.DivisionValues.ConjugateWeightGram.exists_reduced {F : Type} [Field F] {n : ℕ} (Z : Submodule F (Fin n → F)) :
    ∃ (d : ℕ) (z : Fin d → Fin n → F) (f : Fin d → Fin n), LinearIndependent F z ∧
      Submodule.span F (Set.range z) = Z ∧ ∀ a b, z a (f b) = if a = b then 1 else 0 := by sorry
