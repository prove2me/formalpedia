-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_exists_subgroup_thetaGroup_tensor_self_injOn_pt_image_eq_two_torsion
-- name    : AlgebraicGeometry.Polarisation.exists_subgroup_thetaGroup_tensor_self_injOn_pt_image_eq_two_torsion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/9ab0892f-4576-54fa-9f88-b0b8e12d5670
-- title:
--   A level-A[2] subgroup of the theta group of mathcal L₀^{⊗ 2}
-- statement:
--   Let $k$ be an algebraically closed field, let $A$ be a scheme with a morphism $f : A \to \operatorname{Spec} k$, let $L$ be a relative group law for $f$ (a functorial group structure on the sets $\{\varphi : T \to A : \varphi \circ f = t\}$ of $T$-points over $\operatorname{Spec} k$, compatible with base change), and let `hc` assert that $L$ is commutative. Assume `hA`, the bundle of properties saying that $f$ is smooth and proper with connected fibres and admits a relative group law. Let $g$ be a natural number and assume every fibre of $f$ has topological Krull dimension $g$. Let $\mathcal L_0$ be a module on $A$ which is invertible, in the sense that every point has a neighbourhood $U$ with $\mathcal L_0|_U$ isomorphic to the unit module, and assume that for every $Q$ in the additive group $L.\mathrm{AlgPoints}$ of $k$-points of $f$ with $2Q = 0$ the pullback of $\mathcal L_0$ along translation by $Q$ is isomorphic to $\mathcal L_0$. The conclusion is that there is a subgroup $K$ of the theta group of $\mathcal L_0 \otimes \mathcal L_0$ — the group of pairs consisting of an automorphism of the pair $(A, \mathcal L_0 \otimes \mathcal L_0)$ and a point $P$ such that the automorphism induces translation by $P$ on $A$ — such that the projection `pt` to the point is injective on $K$, and such that for every $Q$ the element $Q$ lies in the image of $K$ under `pt` if and only if $2Q = 0$.
--
--   This is the existence of a level structure over $A[2]$ for the theta group of $\mathcal L_0^{\otimes 2}$: a subgroup mapping bijectively onto the $2$-torsion, in the style of Mumford's theory of theta groups of line bundles on abelian varieties. It is used in the construction of a Mumford-type bundle, namely by [`AlgebraicGeometry.Polarisation.exists_nonempty_iso_mumfordBundle_of_mumfordBundle_iso_tensor_self_of_two_ne_zero`](thm.html#AlgebraicGeometry.Polarisation.exists_nonempty_iso_mumfordBundle_of_mumfordBundle_iso_tensor_self_of_two_ne_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_exists_subgroup_thetaGroup_tensor_self_injOn_pt_image_eq_two_torsion.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_ThetaGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RiemannForm AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.exists_subgroup_thetaGroup_tensor_self_injOn_pt_image_eq_two_torsion
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (g : ℕ) (hdim : ∀ s : ↥(Spec (CommRingCat.of k)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g)
    (𝓛₀ : A.Modules) (h𝓛₀ : Scheme.Modules.IsInvertible 𝓛₀)
    (hK2 : ∀ Q : L.AlgPoints hc k, 2 • Q = 0 →
      Nonempty ((Scheme.Modules.pullback (translation f L (RelativeGroupLaw.AlgPoints.toPoint Q))).obj 𝓛₀ ≅ 𝓛₀)) :
    ∃ K : Subgroup (RiemannForm.thetaGroup f L hc (𝓛₀ ⊗ 𝓛₀)),
      (∀ g ∈ K, ∀ h ∈ K, RiemannForm.thetaGroup.pt f L hc (𝓛₀ ⊗ 𝓛₀) g = RiemannForm.thetaGroup.pt f L hc (𝓛₀ ⊗ 𝓛₀) h → g = h) ∧
      (∀ Q : L.AlgPoints hc k, (∃ g ∈ K, RiemannForm.thetaGroup.pt f L hc (𝓛₀ ⊗ 𝓛₀) g = Multiplicative.ofAdd Q) ↔ 2 • Q = 0) := by sorry
