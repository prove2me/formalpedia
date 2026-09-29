-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_mem_kernelPts_iff_nonempty_pullback_translate_iso
-- name    : AlgebraicGeometry.Polarisation.mem_kernelPts_iff_nonempty_pullback_translate_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/b22118c0-3160-5668-a076-c218514b7d8e
-- title:
--   x ∈ K(L) iff Tₓ^*L ≅ L
-- statement:
--   Let $k$ be an algebraically closed field, let $A$ be a scheme with a structure morphism $f : A \to \operatorname{Spec} k$, let $L$ be a relative group law on $f$ — that is, a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ t = \text{(structure map of }T)\}$ of $T$-points of $A$ over $\operatorname{Spec} k$, with multiplication, unit and inverse natural in $T$ — let $\mathcal L$ be an object of `A.Modules`, and let $x$ be a $k$-point of $A$, i.e. a morphism $x : \operatorname{Spec} k \to A$ with $x$ followed by $f$ the identity of $\operatorname{Spec} k$. The assertion is the equivalence of two conditions. First, $x \in$ `kernelPts f L 𝓛`, which by definition is `L.IsInStabilizer 𝓛 (𝟙 (Spec (CommRingCat.of k))) x`: on the fibre product $A \times_{\operatorname{Spec} k} \operatorname{Spec} k$ formed from $f$ and the identity of $\operatorname{Spec} k$, the pullback of $\mathcal L$ along the right-translation morphism `L.mulRight` associated with $x$ and the pullback of $\mathcal L$ along the first projection are `Scheme.Modules.LocallyIsoOver` the second projection, i.e. isomorphic locally over the base. Second, the type of isomorphisms between $(\mathrm{L.translate}\,x)^{*}\mathcal L$ and $\mathcal L$ in `A.Modules` is nonempty, where `L.translate x` is the endomorphism of $A$ obtained by multiplying, in $L$, the identity point of $A$ with the constant point $f$ followed by $x$.
--
--   This identifies the $k$-points of the theta group / stabiliser scheme $K(\mathcal L)$ of a line bundle on an abelian variety, defined here by the relative stabiliser condition on the base change $A \times_k \operatorname{Spec} k$, with the classical condition $T_x^{*}\mathcal L \cong \mathcal L$ on translates. It is the basic bridge used throughout the dual-free treatment of $\operatorname{Pic}^0$ and of the polarisation $\varphi_{\mathcal L}$, and is invoked by the finiteness and $\mathrm{H}^0$-dimension statements about $K(\mathcal L)$ in the same development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_mem_kernelPts_iff_nonempty_pullback_translate_iso.lean

import Definitions.Def_AlgebraicGeometry_PolarisationPicZero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.mem_kernelPts_iff_nonempty_pullback_translate_iso
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (𝓛 : A.Modules) (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    x ∈ kernelPts f L 𝓛 ↔ Nonempty ((Scheme.Modules.pullback (L.translate x)).obj 𝓛 ≅ 𝓛) := by sorry
