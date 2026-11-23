-- Prove2me | Theorems.Thm_Formalism_DivisionValues_exponent_index_lattice_idxB
-- name    : Formalism.DivisionValues.exponent_index_lattice.idxB
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:32:28.450833+00:00
-- url     : https://prove2.me/theorems/53f52147-5579-40fb-b7bd-643d0951df8b
-- title:
--   exponent index lattice: idx B
-- statement:
--   The exponent index lattice construction uses the idx B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/AuxStatement14.lean#L160-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/AuxStatement14.lean#L160-L169

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

theorem Formalism.DivisionValues.exponent_index_lattice.idxB {D : ℕ} (w : HeightOneSpectrum (𝓞 K)) (A B C : Submodule (𝓞 K) (Fin D → K))
    (hA : Submodule.IsLattice K A) (hB : Submodule.IsLattice K B) (hC : Submodule.IsLattice K C) :
    idx w A B = - idx w B A ∧ idx w A C = idx w A B + idx w B C ∧
      (B ≤ A → idx w A B = Formalism.HermitianLatticesTheory.locLen w.asIdeal A B) := by sorry
