-- Prove2me | Theorems.Thm_Formalism_DivisionValues_exponent_index_lattice_Pr_surj
-- name    : Formalism.DivisionValues.exponent_index_lattice.Pr_surj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:33:15.688009+00:00
-- url     : https://prove2.me/theorems/66dd0850-feb2-4145-ad37-7b7eee347308
-- title:
--   exponent index lattice: Pr surj
-- statement:
--   The exponent index lattice construction uses the Pr surj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/AuxStatement14.lean#L117-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/AuxStatement14.lean#L117-L122

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ClassSumDualLe
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_RatHerm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionLemmaFirst
import Definitions.Def_Lemmata_HermitianVanishing_KeyZero
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_AuxStatement14
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
open Formalism.DivisionValues.exponent_index_lattice
variable {K : Type} [Field K] [NumberField K] [StarRing K]
open RationalHermitianForm

theorem Formalism.DivisionValues.exponent_index_lattice.Pr_surj {n d : ℕ} {H : Matrix (Fin n) (Fin n) K}
    {E : Matrix (Fin n) (Fin d) K} {Pr : Matrix (Fin d) (Fin n) K} (hO : IsOrthProj H E Pr) :
    Function.Surjective (Matrix.mulVecLin Pr) := by sorry
