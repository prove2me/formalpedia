-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_finite_kernelPts_of_iso_tensorPow_of_finite_kernelPts
-- name    : AlgebraicGeometry.Polarisation.finite_kernelPts_of_iso_tensorPow_of_finite_kernelPts
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/c4b36e04-28cf-52f3-8418-792cc2dda7c7
-- title:
--   Finiteness of K(N) for N ≅ M^{⊗ n}
-- statement:
--   Let $k$ be an algebraically closed field, $A$ a scheme and $f : A \to \operatorname{Spec} k$ a morphism, and let $L$ be a `RelativeGroupLaw` for $f$, that is, a group structure on the sets $\mathrm{SchemeHomOver}(t, f)$ of $T$-points $x : T \to A$ with $x \circ f = t$, given for every $t : T \to \operatorname{Spec} k$ and compatible with base change along morphisms $\psi : T' \to T$ over $\operatorname{Spec} k$. Assume $L$ is commutative (multiplication on every such point set is commutative), and that $f$ satisfies `AbelianSchemePropertyBundle`: $f$ is smooth and proper, each fibre $f^{-1}(s)$ is connected, and a relative group law exists. Let $\mathcal M$ be an $\mathcal O_A$-module which is invertible in the sense that every point of $A$ has an open neighbourhood $U$ on which the pullback of $\mathcal M$ along $U \hookrightarrow A$ is isomorphic to the unit module, and suppose the set $K(\mathcal M) = \{x \in \mathrm{SchemeHomOver}(\mathrm{id}_{\operatorname{Spec} k}, f) : \text{translation by } x \text{ leaves } \mathcal M \text{ locally unchanged}\}$ — the points $x$ for which the pullback of $\mathcal M$ along right translation by $x$ and its pullback along the first projection are locally isomorphic over the second projection — is finite. Then for every $n > 0$ and every $\mathcal O_A$-module $\mathcal N$ admitting an isomorphism $\mathcal N \cong \mathcal M^{\otimes n}$ (the $n$-fold tensor power built from the unit module by repeated tensoring with $\mathcal M$), the set $K(\mathcal N)$ is finite.
--
--   This is the finiteness half of the standard reduction of the vanishing theorem on an abelian variety to the case of a single invertible sheaf: non-degeneracy of $\mathcal M$, expressed as finiteness of the group of $k$-points of the stabiliser $K(\mathcal M)$, propagates to all positive tensor powers. It feeds the computations of the geometric fibre $H^0$ and of the relevant $H$-groups used later in the polarisation package.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_finite_kernelPts_of_iso_tensorPow_of_finite_kernelPts.lean

import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.finite_kernelPts_of_iso_tensorPow_of_finite_kernelPts
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (𝓜 : A.Modules) (h𝓜 : Scheme.Modules.IsInvertible 𝓜) (hK : (kernelPts f L 𝓜).Finite)
    (n : ℕ) (hn : 0 < n) (𝓝 : A.Modules) (e : 𝓝 ≅ 𝓜.tensorPow n) :
    (kernelPts f L 𝓝).Finite := by sorry
