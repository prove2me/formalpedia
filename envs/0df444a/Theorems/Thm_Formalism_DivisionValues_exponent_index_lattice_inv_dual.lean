-- Prove2me | Theorems.Thm_Formalism_DivisionValues_exponent_index_lattice_inv_dual
-- name    : Formalism.DivisionValues.exponent_index_lattice.inv_dual
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:22:08.494946+00:00
-- url     : https://prove2.me/theorems/d8986820-bd0f-4fea-9c88-053da5bc9343
-- title:
--   exponent index lattice: inv dual
-- statement:
--   The exponent index lattice construction uses the inv dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/AuxStatement14.lean#L471-L495
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/AuxStatement14.lean#L471-L495

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
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  {Γ : Type} [Group Γ] [Fintype Γ] (ρ : Γ →* Module.End K V)

theorem Formalism.DivisionValues.exponent_index_lattice.inv_dual [FiniteDimensional K V] (pair : V →ₗ⋆[K] V →ₗ[K] K) (hs : pair.IsSymm)
    (hn : pair.Nondegenerate) (hiso : ∀ γ x y, pair (ρ γ x) (ρ γ y) = pair x y)
    (A : Submodule (𝓞 K) V) (hA : Submodule.IsLattice K A) :
    Formalism.HermitianLatticesTheory.dual (pair.domRestrict₁₂ (invSub ρ) (invSub ρ))
              (A.comap ((invSub ρ).subtype.restrictScalars (𝓞 K))) =
      (Formalism.HermitianLatticesTheory.dual pair A).map ((avg ρ).restrictScalars (𝓞 K)) := by sorry
