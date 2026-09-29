-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_exists_nonempty_iso_mumfordBundle_of_mumfordBundle_iso_tensor_self_of_two_ne_zero
-- name    : AlgebraicGeometry.Polarisation.exists_nonempty_iso_mumfordBundle_of_mumfordBundle_iso_tensor_self_of_two_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/b3c31526-bf1d-531b-83a1-de58d1141d6f
-- title:
--   Halving a symmetric bi-rigidified square root of a Mumford bundle
-- statement:
--   Let $k$ be an algebraically closed field, $A$ a scheme with a structure morphism $f : A \to \operatorname{Spec} k$, and $L$ a relative group law on $f$, that is, a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ (\text{structure map}) \}$ of $T$-points of $A$ over $\operatorname{Spec} k$, natural in $T$; assume $L$ is commutative. Assume further the property bundle `AbelianSchemePropertyBundle` for $f$: $f$ is smooth and proper, each fibre $f^{-1}(s)$ is connected, and $f$ carries a relative group law. Let $g : \mathbb{N}$ be such that every fibre $f^{-1}(s)$ has topological Krull dimension $g$, and suppose $2 \neq 0$ in $k$. Let $\mathcal{P}$ be a module on $A \times_{\operatorname{Spec} k} A$ which is invertible (locally on the base isomorphic, after pullback along the inclusion of an open, to the unit module). Suppose $\mathcal{P}$ is rigidified along both axes: its pullback along the slice morphism $\operatorname{sliceAt}$ attached to the zero point of $L.\mathrm{AlgPoints}\ hc\ k$ — the map $A \times_{\operatorname{Spec} k} \operatorname{Spec} k \to A \times_{\operatorname{Spec} k} A$ given by the first projection in the first coordinate and the identity section in the second — admits an isomorphism with the unit, and likewise for the pullback of $(\text{swap})^{*}\mathcal{P}$ along that same slice; and $\mathcal{P}$ is symmetric, i.e. $(\text{swap})^{*}\mathcal{P} \cong \mathcal{P}$, where swap is the canonical symmetry of the pullback $A \times_{\operatorname{Spec} k} A$. Finally let $\mathcal{L}_0$ be an invertible module on $A$ whose Mumford bundle $\mathrm{mumfordBundle}\,f\,L\,\mathcal{L}_0 = m^{*}\mathcal{L}_0 \otimes (p_1^{*}\mathcal{L}_0^{\vee} \otimes p_2^{*}\mathcal{L}_0^{\vee})$, with $m$ the addition morphism of $L$ on the two projections and $\mathcal{L}_0^{\vee}$ the internal dual, is isomorphic to $\mathcal{P} \otimes \mathcal{P}$. Then there exists an invertible module $\mathcal{M}$ on $A$ together with an isomorphism $\mathcal{P} \cong \mathrm{mumfordBundle}\,f\,L\,\mathcal{M}$.
--
--   This is the halving step in the identification of symmetric bi-rigidified line bundles on $A \times A$ with Mumford bundles $\Lambda(\mathcal{M})$: a symmetric bi-rigidified $\mathcal{P}$ whose square is a Mumford bundle is itself a Mumford bundle, the passage from $\mathcal{L}_0$ to $\mathcal{M}$ being a descent along multiplication by $2$ via a level-$2$ theta structure, which is why $2$ is required to be invertible. It feeds the statement that symmetric bi-rigidified invertible modules arise from line bundles on $A$, used in the construction of polarisations and the Rosati involution for the Jacobians occurring later in the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_exists_nonempty_iso_mumfordBundle_of_mumfordBundle_iso_tensor_self_of_two_ne_zero.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RiemannForm AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.exists_nonempty_iso_mumfordBundle_of_mumfordBundle_iso_tensor_self_of_two_ne_zero
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (g : ℕ) (hdim : ∀ s : ↥(Spec (CommRingCat.of k)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g)
    (h2 : (2 : k) ≠ 0)
    (𝓟 : (pullback f f).Modules) (h𝓟 : Scheme.Modules.IsInvertible 𝓟)
    (h₁ : Nonempty ((Scheme.Modules.pullback (sliceAt f (RelativeGroupLaw.AlgPoints.toPoint (0 : L.AlgPoints hc k)))).obj 𝓟 ≅ 𝟙_ _))
    (h₂ : Nonempty ((Scheme.Modules.pullback (sliceAt f (RelativeGroupLaw.AlgPoints.toPoint (0 : L.AlgPoints hc k)))).obj
        ((Scheme.Modules.pullback (pullbackSymmetry f f).hom).obj 𝓟) ≅ 𝟙_ _))
    (h₃ : Nonempty ((Scheme.Modules.pullback (pullbackSymmetry f f).hom).obj 𝓟 ≅ 𝓟))
    (𝓛₀ : A.Modules) (h𝓛₀ : Scheme.Modules.IsInvertible 𝓛₀) (hΛ : Nonempty (mumfordBundle f L 𝓛₀ ≅ 𝓟 ⊗ 𝓟)) :
    ∃ 𝓜 : A.Modules, Scheme.Modules.IsInvertible 𝓜 ∧ Nonempty (𝓟 ≅ mumfordBundle f L 𝓜) := by sorry
