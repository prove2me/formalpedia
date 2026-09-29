-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_existsUnique_algEquiv_chartVRing_isPullback_of_act_stdFullLattice_eq
-- name    : CerednikDrinfeld.FormalOmega.existsUnique_algEquiv_chartVRing_isPullback_of_act_stdFullLattice_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/bf9ff60d-500f-55e3-8d8b-2fd1fae95c1b
-- title:
--   Unique vertex-chart automorphism transporting Deligne data
-- statement:
--   Fix a prime $r$ and a discrete valuation ring $\mathcal O$ which is a domain, with an irreducible element $\pi$ whose residue ring $\mathcal O/(\pi)$ has exactly $r$ elements, and let $K_0$ be a field that is a fraction field of $\mathcal O$. Let $g_1 \in \mathrm{GL}_2(K_0)$ be the element whose matrix is $\mathrm{diag}(\pi,1)$, let $g \in \mathrm{GL}_2(K_0)$ and $c \in K_0^\times$ satisfy $g\cdot M_0 = (c\cdot 1)\cdot M_0$ as full lattices, where $M_0 = \mathcal O^2 \subseteq K_0^2$ is `stdFullLattice` and the action is by `latticeMap`, and let $n \in \mathbb N$. Write $A := (\mathrm{chartVRing}\ \mathcal O\ r)/(\pi^{n+1})$, the localisation of $\mathcal O$-polynomials away from `vertexDiscr` reduced modulo the $(n+1)$st power of the image of $\pi$, and $\zeta \in A$ for the image of `chartVRing.ζ`. The assertion is that there is exactly one $\mathcal O$-algebra automorphism $\tau$ of $A$ with the following property: for every commutative $\mathcal O$-algebra $B$, every $\mathcal O$-algebra map $y : A \to B$ and all Deligne data $d, d'$ over $B$ (relative to $\pi$ and $K_0$, i.e. families of $B$-submodules of the base-changed lattices with invertible quotients, monotone, homothety-equivariant and non-degenerate at every prime), if $d$ satisfies $d(M_0) = \langle y(\zeta)\otimes e_0 + 1\otimes e_1\rangle_B$, $d(g_1M_0) =$ the image of $\langle y(\zeta)\otimes e_0 + \pi\otimes e_1\rangle_B$ under the base-changed translation isomorphism `actBaseChange` for $g_1$, and $d$ satisfies `DeligneDatum.EdgeNondegAt` at every prime ideal of $B$ for the pair $(g_1M_0, M_0)$, and if $d'$ satisfies the three corresponding conditions with $y$ replaced by $y \circ \tau$, then $d'$ is the pullback of $d$ along $g^{-1}$, that is $d'(M) = (d(g^{-1}M))$ pulled back along `actBaseChange` for $g^{-1}$, for every full lattice $M$.
--
--   This records the action, at each truncation level $n$, of the stabiliser of the standard vertex of the Bruhat–Tits tree (elements $g$ with $g\mathcal O^2$ homothetic to $\mathcal O^2$) on the vertex chart ring of Drinfeld's formal upper half-plane: the chart coordinate $\zeta$ is transported by a unique $\mathcal O$-algebra automorphism compatible with pulling Deligne data back along $g^{-1}$. It is used in the construction of points of the Mumford glueing levels for a Schottky group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_existsUnique_algEquiv_chartVRing_isPullback_of_act_stdFullLattice_eq.lean

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.existsUnique_algEquiv_chartVRing_isPullback_of_act_stdFullLattice_eq
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
    (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])
    (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (c : K₀ˣ)
    (hg : FullLattice.act g (stdFullLattice K₀) = FullLattice.act (scalarGL c) (stdFullLattice (𝒪 := 𝒪) K₀))
    (n : ℕ) :
    ∃! τ : (chartVRing 𝒪 r ⧸ Ideal.span {(algebraMap 𝒪 (chartVRing 𝒪 r) π) ^ (n + 1)}) ≃ₐ[𝒪]
        (chartVRing 𝒪 r ⧸ Ideal.span {(algebraMap 𝒪 (chartVRing 𝒪 r) π) ^ (n + 1)}),
      ∀ (B : Type) [CommRing B] [Algebra 𝒪 B]
        (y : (chartVRing 𝒪 r ⧸ Ideal.span {(algebraMap 𝒪 (chartVRing 𝒪 r) π) ^ (n + 1)}) →ₐ[𝒪] B)
        (d d' : DeligneDatum (K := K₀) π B),
        (d.line (stdFullLattice K₀) =
            Submodule.span B {(y (Ideal.Quotient.mk _ (chartVRing.ζ 𝒪 r))) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
          d.line (FullLattice.act g₁ (stdFullLattice K₀)) =
            (Submodule.span B {(y (Ideal.Quotient.mk _ (chartVRing.ζ 𝒪 r))) ⊗ₜ[𝒪] stdBasisVec K₀ 0 +
                (algebraMap 𝒪 B π) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
          d.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) →
        (d'.line (stdFullLattice K₀) =
            Submodule.span B {((y.comp τ.toAlgHom) (Ideal.Quotient.mk _ (chartVRing.ζ 𝒪 r))) ⊗ₜ[𝒪] stdBasisVec K₀ 0 +
              (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
          d'.line (FullLattice.act g₁ (stdFullLattice K₀)) =
            (Submodule.span B {((y.comp τ.toAlgHom) (Ideal.Quotient.mk _ (chartVRing.ζ 𝒪 r))) ⊗ₜ[𝒪] stdBasisVec K₀ 0 +
                (algebraMap 𝒪 B π) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
          d'.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) →
        DeligneDatum.IsPullback (K := K₀) (π := π) B g⁻¹ d d' := by sorry
