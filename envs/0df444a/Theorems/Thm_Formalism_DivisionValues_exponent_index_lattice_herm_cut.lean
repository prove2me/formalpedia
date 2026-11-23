-- Prove2me | Theorems.Thm_Formalism_DivisionValues_exponent_index_lattice_herm_cut
-- name    : Formalism.DivisionValues.exponent_index_lattice.herm_cut
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:33:34.926933+00:00
-- url     : https://prove2.me/theorems/a3c120a8-a872-4b0e-b163-527e2b740e56
-- title:
--   exponent index lattice: herm cut
-- statement:
--   The exponent index lattice construction uses the herm cut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/AuxStatement14.lean#L82-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/AuxStatement14.lean#L82-L84

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

theorem Formalism.DivisionValues.exponent_index_lattice.herm_cut {n d : ℕ} {H : Matrix (Fin n) (Fin n) K} (hH : Hᴴ = H)
    (E : Matrix (Fin n) (Fin d) K) : (Eᴴ * H * E)ᴴ = Eᴴ * H * E := by sorry
