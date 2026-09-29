-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_exists_inPicZero_tensorPow_iso_unit_not_nonempty_pullback_iso_unit_of_isClosedImmersion
-- name    : AlgebraicGeometry.Polarisation.exists_inPicZero_tensorPow_iso_unit_not_nonempty_pullback_iso_unit_of_isClosedImmersion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/2884bd15-451b-5a71-802d-be443519f7b5
-- title:
--   Torsion element of Pic⁰(A) non-trivial on a subscheme Y
-- statement:
--   Let $k$ be an algebraically closed field, let $f : A \to \operatorname{Spec} k$ be a scheme over $k$, and let $L$ be a relative group law for $f$, i.e. a functorial group structure (multiplication, unit, inverse, associativity, unit and inverse laws, and compatibility with base change along maps $T' \to T$ over $k$) on the sets $\{\varphi : T \to A \mid \varphi \circ t = t\}$ of sections of $f$ over arbitrary $t : T \to \operatorname{Spec} k$; assume `AbelianSchemePropertyBundle k f`, that is, $f$ is smooth and proper, each fibre $f^{-1}(s)$ is connected, and $f$ admits some relative group law. Let $fY : Y \to \operatorname{Spec} k$ be a second such scheme, equipped with a relative group law $LY$ and satisfying the same bundle of properties, and let $j : Y \to A$ be a closed immersion with $j$ followed by $f$ equal to $fY$ which is a homomorphism in the sense that for all $t : T \to \operatorname{Spec} k$ and all sections $P, Q$ of $fY$ over $t$, the section $LY.\mathrm{mul}\,t\,P\,Q$ followed by $j$ equals $L.\mathrm{mul}$ applied to $P$ followed by $j$ and $Q$ followed by $j$. Suppose finally that $n \ge 1$ is a natural number with $\operatorname{topologicalKrullDim} Y = n$. Then there is a module $Q$ on $A$ such that: $Q$ satisfies `InPicZero f L`, i.e. $Q$ is invertible (every point of $A$ has an open neighbourhood $U$ with $Q|_U$ isomorphic to the unit sheaf of modules on $U$) and for every $k$-point $x$ of $A$ the pullback of $Q$ along the translation $L.\mathrm{translate}\,x$ is isomorphic to $Q$; there is an $m > 0$ with $Q^{\otimes m}$, formed by the recursive tensor power, isomorphic to the unit object of the modules on $A$; and the pullback of $Q$ along $j$ is not isomorphic to the unit object of the modules on $Y$.
--
--   This is the statement that a positive-dimensional abelian subvariety of an abelian variety is detected by $\mathrm{Pic}^0$: some torsion element of $\mathrm{Pic}^0(A)$ restricts non-trivially to $Y$, obtained classically from the theorem of the square applied to a polarising invertible sheaf together with the density of torsion points. It is used in the proof of [`GoodReductionJacobian.RelativeGroupLaw.exists_isClosedImmersion_isFinite_forall_iff_isInStabilizer_of_eulerChar_ne_zero`](thm.html#GoodReductionJacobian.RelativeGroupLaw.exists_isClosedImmersion_isFinite_forall_iff_isInStabilizer_of_eulerChar_ne_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_exists_inPicZero_tensorPow_iso_unit_not_nonempty_pullback_iso_unit_of_isClosedImmersion.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.exists_inPicZero_tensorPow_iso_unit_not_nonempty_pullback_iso_unit_of_isClosedImmersion
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hA : AbelianSchemePropertyBundle k f)
    {Y : Scheme.{0}} (fY : Y ⟶ Spec (CommRingCat.of k)) (j : Y ⟶ A) [IsClosedImmersion j] (hjf : j ≫ f = fY)
    (LY : RelativeGroupLaw k fY) (hY : AbelianSchemePropertyBundle k fY)
    (hj : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t fY),
      (LY.mul t P Q).1 ≫ j =
        (L.mul t ⟨P.1 ≫ j, by rw [Category.assoc, hjf, P.2]⟩ ⟨Q.1 ≫ j, by rw [Category.assoc, hjf, Q.2]⟩).1)
    (n : ℕ) (hn : 1 ≤ n) (hdimY : topologicalKrullDim ↥Y = n) :
    ∃ Q : A.Modules, InPicZero f L Q ∧ (∃ m : ℕ, 0 < m ∧ Nonempty (Q.tensorPow m ≅ 𝟙_ A.Modules)) ∧
      ¬ Nonempty ((Scheme.Modules.pullback j).obj Q ≅ 𝟙_ Y.Modules) := by sorry
