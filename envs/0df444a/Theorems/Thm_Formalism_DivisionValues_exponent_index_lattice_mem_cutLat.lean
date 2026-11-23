-- Prove2me | Theorems.Thm_Formalism_DivisionValues_exponent_index_lattice_mem_cutLat
-- name    : Formalism.DivisionValues.exponent_index_lattice.mem_cutLat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:32:19.82709+00:00
-- url     : https://prove2.me/theorems/9ec859e4-23f7-49eb-b2c5-067afdda0fb6
-- title:
--   exponent index lattice: mem cut Lat
-- statement:
--   The exponent index lattice construction uses the mem cut Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/AuxStatement14.lean#L299-L300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/AuxStatement14.lean#L299-L300

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
open exponent_index_lattice RationalHermitianForm
open Formalism.DivisionValues.exponent_index_lattice
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem Formalism.DivisionValues.exponent_index_lattice.mem_cutLat {n d : ℕ} (E : Matrix (Fin n) (Fin d) K) (A : Submodule (𝓞 K) (Fin n → K))
    (z : Fin d → K) : z ∈ cutLat E A ↔ E.mulVec z ∈ A := by sorry
