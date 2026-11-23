-- Prove2me | Theorems.Thm_Formalism_DivisionValues_R0_conjTranspose_eq_of_posDef
-- name    : Formalism.DivisionValues.R0.conjTranspose_eq_of_posDef
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:17:27.795824+00:00
-- url     : https://prove2.me/theorems/cca19bf4-8252-4372-af81-f076f937ef09
-- title:
--   R0: conj Transpose eq of pos Def
-- statement:
--   The R0 construction uses the conj Transpose eq of pos Def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ConjTransposeEqOfPosDef.lean#L35-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ConjTransposeEqOfPosDef.lean#L35-L42

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjTransposeEqOfPosDef
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
open Formalism.DivisionValues.R0
variable {K : Type} [Field K] [StarRing K]

theorem Formalism.DivisionValues.R0.conjTranspose_eq_of_posDef [NumberField K] (v0 : InfinitePlace K) (hv0 : IsConjAt v0)
    {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (hH : (H.map v0.embedding).PosDef) : Hᴴ = H := by sorry
