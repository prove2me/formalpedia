-- Prove2me | Theorems.Thm_Formalism_DivisionValues_ConjugateWeightLattice_gen_iff
-- name    : Formalism.DivisionValues.ConjugateWeightLattice.gen_iff
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:24:52.464222+00:00
-- url     : https://prove2.me/theorems/f7f477db-6872-4c19-900e-1599a21ba1cc
-- title:
--   Conjugate Weight Lattice: gen iff
-- statement:
--   The Conjugate Weight Lattice construction uses the gen iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/JwConj.lean#L19-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/JwConj.lean#L19-L29

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_RatHerm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_JwConj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.ConjugateWeightLattice
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem Formalism.DivisionValues.ConjugateWeightLattice.gen_iff (p : Ideal (𝓞 K)) (s : 𝓞 K) :
    (s ∉ p ∧ ∀ t : 𝓞 K, algebraMap (𝓞 K) K t = star (algebraMap (𝓞 K) K s) → t ∉ p) ↔
      (s ∉ p ∧ cO K s ∉ p) := by sorry
