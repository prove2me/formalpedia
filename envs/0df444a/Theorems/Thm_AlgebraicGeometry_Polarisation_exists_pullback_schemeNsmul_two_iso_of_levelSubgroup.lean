-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_exists_pullback_schemeNsmul_two_iso_of_levelSubgroup
-- name    : AlgebraicGeometry.Polarisation.exists_pullback_schemeNsmul_two_iso_of_levelSubgroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/9eaadd31-fb9e-5f6f-9ee3-bf2928e91384
-- title:
--   Descent of an invertible module along [2] from a level subgroup
-- statement:
--   Let $k$ be an algebraically closed field, let $f : A \to \operatorname{Spec} k$ be a morphism of schemes, and let $L$ be a relative group law for $f$, that is, a functorially compatible group structure on the sets of $T$-points of $A$ over $\operatorname{Spec} k$; assume $L$ is commutative, and that $f$ satisfies `AbelianSchemePropertyBundle`, i.e. $f$ is smooth and proper, each fibre $f^{-1}(s)$ is connected, and $f$ admits a relative group law. Assume further that for some natural number $g$ every fibre $f^{-1}(s)$ has topological Krull dimension $g$, and that $2 \neq 0$ in $k$. Let $\mathcal L_0$ be a module on $A$ that is invertible, in the sense that every point of $A$ has an open neighbourhood over which $\mathcal L_0$ pulls back to the unit module. Let $K$ be a subgroup of the theta group of $\mathcal L_0$, the group of pairs consisting of an automorphism of the pair $(A,\mathcal L_0)$ and a point $P$ of $A(k)$ (written multiplicatively) such that the underlying morphism of $A$ is translation by $P$. Assume the point map `RiemannForm.thetaGroup.pt` is injective on $K$, and that a point $Q \in A(k)$ lies in the image of $K$ under this map exactly when $2Q = 0$. Then there is an invertible module $\mathcal M'$ on $A$ whose pullback along the multiplication-by-$2$ morphism $L.\mathrm{schemeNsmul}\,2 : A \to A$ is isomorphic to $\mathcal L_0$.
--
--   This is the descent step in Mumford's theory of theta groups: a level subgroup above the $2$-torsion turns $\mathcal L_0$ into the pullback of an invertible module along $[2]$. It is used in the construction of Mumford bundles, in particular by [`AlgebraicGeometry.Polarisation.exists_nonempty_iso_mumfordBundle_of_mumfordBundle_iso_tensor_self_of_two_ne_zero`](thm.html#AlgebraicGeometry.Polarisation.exists_nonempty_iso_mumfordBundle_of_mumfordBundle_iso_tensor_self_of_two_ne_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_exists_pullback_schemeNsmul_two_iso_of_levelSubgroup.lean

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

theorem AlgebraicGeometry.Polarisation.exists_pullback_schemeNsmul_two_iso_of_levelSubgroup
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (g : ℕ) (hdim : ∀ s : ↥(Spec (CommRingCat.of k)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g)
    (h2 : (2 : k) ≠ 0)
    (𝓛₀ : A.Modules) (h𝓛₀ : Scheme.Modules.IsInvertible 𝓛₀)
    (K : Subgroup (RiemannForm.thetaGroup f L hc 𝓛₀))
    (hKinj : ∀ g ∈ K, ∀ h ∈ K, RiemannForm.thetaGroup.pt f L hc 𝓛₀ g = RiemannForm.thetaGroup.pt f L hc 𝓛₀ h → g = h)
    (hKpt : ∀ Q : L.AlgPoints hc k, (∃ g ∈ K, RiemannForm.thetaGroup.pt f L hc 𝓛₀ g = Multiplicative.ofAdd Q) ↔ 2 • Q = 0) :
    ∃ 𝓜' : A.Modules, Scheme.Modules.IsInvertible 𝓜' ∧
      Nonempty ((Scheme.Modules.pullback (L.schemeNsmul 2)).obj 𝓜' ≅ 𝓛₀) := by sorry
