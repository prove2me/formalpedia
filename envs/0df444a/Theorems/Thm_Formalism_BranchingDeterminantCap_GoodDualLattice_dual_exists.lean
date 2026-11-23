-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_GoodDualLattice_dual_exists
-- name    : Formalism.BranchingDeterminantCap.GoodDualLattice.dual_exists
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:16:54.746377+00:00
-- url     : https://prove2.me/theorems/20350daa-7f21-4b06-9e56-82431c4272a0
-- title:
--   Good Dual Lattice: dual exists
-- statement:
--   The Good Dual Lattice construction uses the dual exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/GoodDual.lean#L54-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/GoodDual.lean#L54-L159

import Definitions.Def_Formalism_BranchSandwichDivisors_StatementL
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_RatHerm
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_GoodDual
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
open Formalism Formalism.BranchingDeterminantCap
open Formalism.BranchingDeterminantCap.GoodDualLattice
variable {R K V : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [StarRing K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem Formalism.BranchingDeterminantCap.GoodDualLattice.dual_exists [FiniteDimensional K V] (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hnd : ∀ x, (∀ y, h y x = 0) → x = 0) (e : V →ₗ[K] V) (hee : ∀ x, e (e x) = e x)
    (hsa : ∀ x y, h (e x) y = h x (e y)) (A : Submodule R V) (hfg : A.FG)
    (hsp : Submodule.span K (A : Set V) = ⊤) (x : V) (hxe : e x = x)
    (hx : ∀ y ∈ A, e y = y → h y x ∈ (1 : Submodule R K)) :
    ∃ z : V, (∀ y ∈ A, h y z ∈ (1 : Submodule R K)) ∧ e z = x := by sorry
