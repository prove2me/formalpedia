-- Prove2me | Theorems.Thm_Formalism_DivisionValues_ConjugateWeightGram_exists_frame
-- name    : Formalism.DivisionValues.ConjugateWeightGram.exists_frame
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:18:22.596266+00:00
-- url     : https://prove2.me/theorems/47d00516-4c1b-47bf-816e-ede5fb1d676a
-- title:
--   Conjugate Weight Gram: exists frame
-- statement:
--   The Conjugate Weight Gram construction uses the exists frame property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ConjugateWeightLatticeOfGeneral.lean#L730-L739
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ConjugateWeightLatticeOfGeneral.lean#L730-L739

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
open StepBAux
variable {K : Type} [Field K] [NumberField K] [StarRing K]
open scoped MatrixOrder

theorem Formalism.DivisionValues.ConjugateWeightGram.exists_frame {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.PosDef) :
    ∃ Y : Matrix (Fin d) (Fin d) ℂ, IsUnit Y.det ∧ (Y⁻¹)ᴴ * Y⁻¹ = A := by sorry
