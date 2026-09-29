-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_MumfordGlueCore_exists_isPullback_of_zeta_comp_eq_of_isUnit_eta
-- name    : CerednikDrinfeld.FormalOmega.MumfordGlueCore.exists_isPullback_of_zeta_comp_eq_of_isUnit_eta
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/8cef8a11-7410-5f50-a87f-f6e8e4171640
-- title:
--   Equal chart points with η invertible give N-related Deligne data
-- statement:
--   Fix a prime $r$, a commutative domain $\mathcal O$ assumed (as an explicit hypothesis) to be a discrete valuation ring, an irreducible element $\pi \in \mathcal O$ with $\#(\mathcal O/(\pi)) = r$, a fraction field $K_0$ of $\mathcal O$, and $g_1 \in \mathrm{GL}_2(K_0)$ whose matrix is $\mathrm{diag}(\pi, 1)$. Let $N \le \mathrm{PGL}(2,K_0)$ be a subgroup acting on the Bruhat–Tits tree of $(\mathcal O,K_0)$ in Schottky fashion (trivial vertex stabilisers, no dart sent to its reverse, finitely many vertex and dart orbits) and contained in the subgroup preserving the parity of the distance to the standard vertex, and let $M$ be a Mumford gluing core for $(\mathcal O,\pi,K_0,r,g_1,N)$. The assertion is: for every level $n$, every commutative local ring $B$ that is an $\mathcal O$-algebra, all $h,h' \in \mathrm{GL}_2(K_0)$, all $\mathcal O$-algebra maps $x_q, x_q'$ from the truncated edge chart ring $(\mathrm{chartERing}\,\mathcal O\,\pi\,r)/(\pi^{n+1})$ to $B$, and all Deligne data $d, d', P, P'$ over $B$, assume: the line of $d$ at the standard full lattice $L_0$ is the $B$-span of $x_q(\bar\xi)\otimes e_0 + 1\otimes e_1$, its line at $g_1 L_0$ is the image under $\mathrm{actBaseChange}\,B\,g_1\,L_0$ of the span of $1\otimes e_0 + x_q(\bar\eta)\otimes e_1$, and $d$ satisfies $\mathrm{InEdgeChart}$ for the pair $(g_1L_0, L_0)$, i.e. the edge-nondegeneracy conditions hold at every prime ideal of $B$; the same three conditions for $d'$ with $x_q'$; $P$ is the pullback of $d$ along $h^{-1}$ and $P'$ the pullback of $d'$ along $h'^{-1}$, in the sense that $P.\mathrm{line}\,M$ is the preimage of $d.\mathrm{line}(h^{-1}M)$ under $\mathrm{actBaseChange}\,B\,h^{-1}\,M$ for every full lattice $M$, and likewise for $P'$; $x_q'(\bar\eta)$ is a unit of $B$; there is some $g \in \mathrm{GL}_2(K_0)$ with class in $N$ such that $h'g_1$ and $gh$, or $h'g_1$ and $ghg_1$, send the standard vertex to the same vertex; and $\mathrm{Spec}$ of $x_q$ followed by $M.\zeta\,h\,n$ equals $\mathrm{Spec}$ of $x_q'$ followed by $M.\zeta\,h'\,n$. Then there exists $g \in \mathrm{GL}_2(K_0)$ whose class lies in $N$ with $P'$ the pullback of $P$ along $g^{-1}$.
--
--   This is one case of the forward direction of Mumford's local dictionary for the chart gluing of the formal upper half-plane: two chart points with the same image in the glued scheme carry Deligne data differing by an element of $N$. It treats the case in which the closed point of $\mathrm{Spec}\,B$ lies over the far end of the second edge, recorded by invertibility of $x_q'(\bar\eta)$, and is used, alongside the companion case with $\bar\xi$ invertible, by [`CerednikDrinfeld.FormalOmega.MumfordGlueCore.exists_isPullback_of_zeta_comp_eq_of_isLocalRing`](thm.html#CerednikDrinfeld.FormalOmega.MumfordGlueCore.exists_isPullback_of_zeta_comp_eq_of_isLocalRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_MumfordGlueCore_exists_isPullback_of_zeta_comp_eq_of_isUnit_eta.lean

import Definitions.Def_CerednikDrinfeld_MumfordGlueCore
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_MumfordVertexType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Mumford

theorem CerednikDrinfeld.FormalOmega.MumfordGlueCore.exists_isPullback_of_zeta_comp_eq_of_isUnit_eta
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
    (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])
    (N : Subgroup (PGL(2, K₀)))
    (hN : IsSchottky (↥N) (BruhatTits.tree 𝒪 K₀))
    (hNtype : N ≤ typePreserving (PGL(2, K₀)) (BruhatTits.tree 𝒪 K₀) (LT.LatticeTree.stdVertex 𝒪 K₀))
    (M : MumfordGlueCore 𝒪 π K₀ r g₁ N) :
    ∀ (n : ℕ) (B : Type) [CommRing B] [IsLocalRing B] [Algebra 𝒪 B]
    (h h' : Matrix.GeneralLinearGroup (Fin 2) K₀) (xq xq' : ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})) →ₐ[𝒪] B) (d d' P P' : DeligneDatum (K := K₀) π B),
    (d.line (stdFullLattice K₀) =
          Submodule.span B {((xq.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.ξ 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
        d.line (FullLattice.act g₁ (stdFullLattice K₀)) =
          (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + ((xq.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.η 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
            (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
        d.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) →
    (d'.line (stdFullLattice K₀) =
          Submodule.span B {((xq'.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.ξ 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
        d'.line (FullLattice.act g₁ (stdFullLattice K₀)) =
          (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + ((xq'.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.η 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
            (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
        d'.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) →
    DeligneDatum.IsPullback (K := K₀) (π := π) B h⁻¹ d P → DeligneDatum.IsPullback (K := K₀) (π := π) B h'⁻¹ d' P' →
    IsUnit (xq' (Ideal.Quotient.mk _ (chartERing.η 𝒪 π r))) →
    (∃ g : Matrix.GeneralLinearGroup (Fin 2) K₀, Matrix.ProjGenLinGroup.mk g ∈ N ∧
      (Vertex.act h' (Vertex.act g₁ (stdVertex 𝒪 K₀)) = Vertex.act (g * h) (stdVertex 𝒪 K₀) ∨ Vertex.act h' (Vertex.act g₁ (stdVertex 𝒪 K₀)) = Vertex.act (g * h) (Vertex.act g₁ (stdVertex 𝒪 K₀)))) →
    Spec.map (CommRingCat.ofHom xq.toRingHom) ≫ M.ζ h n = Spec.map (CommRingCat.ofHom xq'.toRingHom) ≫ M.ζ h' n →
      ∃ g : Matrix.GeneralLinearGroup (Fin 2) K₀, Matrix.ProjGenLinGroup.mk g ∈ N ∧ DeligneDatum.IsPullback (K := K₀) (π := π) B g⁻¹ P P' := by sorry
