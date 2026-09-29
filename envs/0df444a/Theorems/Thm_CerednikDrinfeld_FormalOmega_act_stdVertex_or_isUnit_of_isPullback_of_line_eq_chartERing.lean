-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_act_stdVertex_or_isUnit_of_isPullback_of_line_eq_chartERing
-- name    : CerednikDrinfeld.FormalOmega.act_stdVertex_or_isUnit_of_isPullback_of_line_eq_chartERing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/a53de5dd-2d24-539f-be50-35355927553b
-- title:
--   Edge-chart incidence for translated Deligne data
-- statement:
--   Let $r$ be a prime, let $\mathcal O$ be a commutative domain assumed (as an explicit hypothesis) to be a discrete valuation ring, let $\pi \in \mathcal O$ be irreducible with $\#(\mathcal O/(\pi)) = r$, and let $K_0$ be a field that is an $\mathcal O$-algebra and a fraction field of $\mathcal O$. Let $g_1 \in \mathrm{GL}_2(K_0)$ have underlying matrix $\mathrm{diag}(\pi,1)$, let $n \in \mathbb N$, and let $B$ be a local commutative $\mathcal O$-algebra. Let $xq, xq'$ be $\mathcal O$-algebra maps from `chartERing 𝒪 π r` $/(\pi^{n+1})$ — the localisation of the edge quotient ring away from `edgeQuot.discr`, reduced modulo the $(n+1)$st power of the image of $\pi$ — to $B$, and let $d, d'$ be Deligne data over $B$ (data of a $B$-submodule `line M` of the base change of each full lattice $M \subset K_0^2$, with invertible quotient, monotone, homothety-equivariant and non-degenerate in the sense of the structure `DeligneDatum`). Assume for $d$, with $\xi, \eta$ the chart generators and $e_0, e_1$ the standard basis vectors of the standard lattice: $d.\mathrm{line}$ of the standard full lattice is the $B$-span of $xq(\bar\xi) \otimes e_0 + 1 \otimes e_1$; $d.\mathrm{line}$ of $g_1 \cdot$ (standard lattice) is the image, under the base-changed action of $g_1$, of the span of $1 \otimes e_0 + xq(\bar\eta) \otimes e_1$; and `d.InEdgeChart π (g₁ · std) std` holds, i.e. $d$ satisfies the predicate `EdgeNondegAt` for this pair of lattices at every prime ideal of $B$. Assume the same three clauses for $d'$ with $xq'$ in place of $xq$. Finally let $k \in \mathrm{GL}_2(K_0)$ satisfy `DeligneDatum.IsPullback B k⁻¹ d d'`: for every full lattice $M$, $d'.\mathrm{line}(M)$ is the preimage of $d.\mathrm{line}(k^{-1}\cdot M)$ under the base-changed action of $k^{-1}$. Write $s_0$ for the standard vertex (homothety class of $\mathcal O^2$) and $s_1 = g_1 \cdot s_0$. Then at least one of the following holds: $k$ preserves the unordered pair $\{s_0,s_1\}$, that is either $k s_0 = s_0$ and $k s_1 = s_1$, or $k s_0 = s_1$ and $k s_1 = s_0$; or $k s_0 = s_0$ and both $xq(\bar\xi)$ and $xq'(\bar\xi)$ are units in $B$; or $k s_0 = s_1$ and $xq(\bar\xi)$, $xq'(\bar\eta)$ are units; or $k s_1 = s_0$ and $xq(\bar\eta)$, $xq'(\bar\xi)$ are units; or $k s_1 = s_1$ and $xq(\bar\eta)$, $xq'(\bar\eta)$ are units.
--
--   This is the incidence relation between the edge regions of Drinfeld's formal upper half plane in Deligne-datum form: a point lying in both the standard edge chart and its translate by $k$ forces either that $k$ stabilises the standard edge (possibly flipping it) or that the point lies in one of the two vertex regions $D(\xi)$, $D(\eta)$ of the chart, matched up with the corresponding vertex of the translated edge. It is used in the Mumford-style gluing step, by [`CerednikDrinfeld.FormalOmega.MumfordGlueCore.exists_isPullback_of_zeta_comp_eq_of_edge_rel`](thm.html#CerednikDrinfeld.FormalOmega.MumfordGlueCore.exists_isPullback_of_zeta_comp_eq_of_edge_rel) and [`CerednikDrinfeld.FormalOmega.MumfordGlueCore.zeta_comp_eq_of_exists_isPullback_of_isLocalRing`](thm.html#CerednikDrinfeld.FormalOmega.MumfordGlueCore.zeta_comp_eq_of_exists_isPullback_of_isLocalRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_act_stdVertex_or_isUnit_of_isPullback_of_line_eq_chartERing.lean

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.act_stdVertex_or_isUnit_of_isPullback_of_line_eq_chartERing
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
    (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])
    (n : ℕ) (B : Type) [CommRing B] [IsLocalRing B] [Algebra 𝒪 B]
    (xq xq' : ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})) →ₐ[𝒪] B) (d d' : DeligneDatum (K := K₀) π B)
    (hd : (d.line (stdFullLattice K₀) =
          Submodule.span B {((xq.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.ξ 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
        d.line (FullLattice.act g₁ (stdFullLattice K₀)) =
          (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + ((xq.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.η 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
            (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
        d.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)))
    (hd' : (d'.line (stdFullLattice K₀) =
          Submodule.span B {((xq'.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.ξ 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
        d'.line (FullLattice.act g₁ (stdFullLattice K₀)) =
          (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + ((xq'.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.η 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
            (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
        d'.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)))
    (k : Matrix.GeneralLinearGroup (Fin 2) K₀)
    (hk : DeligneDatum.IsPullback (K := K₀) (π := π) B k⁻¹ d d') :
    ((Vertex.act k (stdVertex 𝒪 K₀) = (stdVertex 𝒪 K₀) ∧ Vertex.act k (Vertex.act g₁ (stdVertex 𝒪 K₀)) = (Vertex.act g₁ (stdVertex 𝒪 K₀))) ∨ (Vertex.act k (stdVertex 𝒪 K₀) = (Vertex.act g₁ (stdVertex 𝒪 K₀)) ∧ Vertex.act k (Vertex.act g₁ (stdVertex 𝒪 K₀)) = (stdVertex 𝒪 K₀))) ∨
    (Vertex.act k (stdVertex 𝒪 K₀) = (stdVertex 𝒪 K₀) ∧ IsUnit (xq (Ideal.Quotient.mk _ (chartERing.ξ 𝒪 π r))) ∧ IsUnit (xq' (Ideal.Quotient.mk _ (chartERing.ξ 𝒪 π r)))) ∨
    (Vertex.act k (stdVertex 𝒪 K₀) = (Vertex.act g₁ (stdVertex 𝒪 K₀)) ∧ IsUnit (xq (Ideal.Quotient.mk _ (chartERing.ξ 𝒪 π r))) ∧ IsUnit (xq' (Ideal.Quotient.mk _ (chartERing.η 𝒪 π r)))) ∨
    (Vertex.act k (Vertex.act g₁ (stdVertex 𝒪 K₀)) = (stdVertex 𝒪 K₀) ∧ IsUnit (xq (Ideal.Quotient.mk _ (chartERing.η 𝒪 π r))) ∧ IsUnit (xq' (Ideal.Quotient.mk _ (chartERing.ξ 𝒪 π r)))) ∨
    (Vertex.act k (Vertex.act g₁ (stdVertex 𝒪 K₀)) = (Vertex.act g₁ (stdVertex 𝒪 K₀)) ∧ IsUnit (xq (Ideal.Quotient.mk _ (chartERing.η 𝒪 π r))) ∧ IsUnit (xq' (Ideal.Quotient.mk _ (chartERing.η 𝒪 π r)))) := by sorry
