-- Prove2me | Theorems.Thm_Formalism_DivisionValues_exponent_index_lattice_cut_isLattice
-- name    : Formalism.DivisionValues.exponent_index_lattice.cut_isLattice
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:32:18.884784+00:00
-- url     : https://prove2.me/theorems/536ff81e-7f29-4e0e-bf13-02f349b69c3e
-- title:
--   exponent index lattice: cut is Lattice
-- statement:
--   The exponent index lattice construction uses the cut is Lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/AuxStatement14.lean#L309-L333
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/AuxStatement14.lean#L309-L333

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

theorem Formalism.DivisionValues.exponent_index_lattice.cut_isLattice {n d : ℕ} (E : Matrix (Fin n) (Fin d) K)
    (hE : Function.Injective (Matrix.mulVecLin E)) (A : Submodule (𝓞 K) (Fin n → K))
    (hA : Submodule.IsLattice K A) : Submodule.IsLattice K (cutLat E A) := by sorry
