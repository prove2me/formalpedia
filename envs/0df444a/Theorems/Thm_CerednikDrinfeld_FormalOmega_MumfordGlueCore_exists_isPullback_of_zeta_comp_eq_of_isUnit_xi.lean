-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_MumfordGlueCore_exists_isPullback_of_zeta_comp_eq_of_isUnit_xi
-- name    : CerednikDrinfeld.FormalOmega.MumfordGlueCore.exists_isPullback_of_zeta_comp_eq_of_isUnit_xi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/fa7c89f7-e0aa-5294-9345-a57f4563b959
-- title:
--   Equal chart points with unit ξ give N-related data
-- statement:
--   Let $r$ be a prime, let $\mathcal O$ be a discrete valuation domain with uniformiser $\pi$ (an irreducible element) whose residue ring $\mathcal O/(\pi)$ has cardinality $r$, and let $K_0$ be its fraction field. Let $g_1 \in \mathrm{GL}_2(K_0)$ be given by the diagonal matrix $\mathrm{diag}(\pi,1)$, and let $N \le \mathrm{PGL}_2(K_0)$ act on the Bruhat–Tits tree of $\mathcal O$-lattice classes in $K_0^2$ as a Schottky group (trivial vertex stabilisers, no dart is sent to its reverse, finitely many orbits of vertices and of darts) and preserve the parity of the distance to the standard vertex $s_0 = [\mathcal O^2]$. Fix a Mumford gluing core $M$ for the data $(\mathcal O,\pi,K_0,r,g_1,N)$, consisting of the truncated schemes $Z_n$ over $\mathcal O/(\pi^{n+1})$ with transition and chart maps $\zeta_{h,n}$. The assertion is: for every level $n$, every local commutative $\mathcal O$-algebra $B$, all $h,h' \in \mathrm{GL}_2(K_0)$, all $\mathcal O$-algebra maps $x_q,x_q'$ from the truncated edge chart ring $A_n = (\text{chartERing}\ \mathcal O\ \pi\ r)/(\pi^{n+1})$ to $B$, and all Deligne data $d,d',P,P'$ over $B$ for $\pi$ (assignments of a $B$-submodule of $B \otimes_{\mathcal O} M$ to each full lattice $M$, with invertible quotient, monotone under inclusions, equivariant for scalar homotheties, and non-degenerate at every prime of $B$), the following holds. Assume $d$ is in standard edge position for $x_q$: its line at the standard full lattice $L_0$ is $B\cdot\bigl(x_q(\xi) \otimes e_0 + 1 \otimes e_1\bigr)$, its line at $g_1 L_0$ is the image under the base-changed action of $g_1$ of $B\cdot\bigl(1 \otimes e_0 + x_q(\eta) \otimes e_1\bigr)$ (with $\xi,\eta$ the generators of the edge chart ring read through $A_n$), and $d$ satisfies the edge-chart non-degeneracy condition for the pair $(g_1L_0, L_0)$ at every prime ideal of $B$; assume the same three conditions for $d'$ with $x_q'$. Assume $P$ is the pullback of $d$ along $h^{-1}$ and $P'$ the pullback of $d'$ along $h'^{-1}$, i.e. for every full lattice $M$ one has $P.\mathrm{line}(M) = (d.\mathrm{line}(h^{-1}M))$ pulled back along the base-changed action of $h^{-1}$, and likewise for $P'$. Assume further that $x_q'(\xi)$ is a unit of $B$, and that there exists $g \in \mathrm{GL}_2(K_0)$ whose class lies in $N$ with $h' s_0 = g h s_0$ or $h' s_0 = g h g_1 s_0$. Then, if $\mathrm{Spec}(x_q)$ followed by $\zeta_{h,n}$ equals $\mathrm{Spec}(x_q')$ followed by $\zeta_{h',n}$, there exists $g \in \mathrm{GL}_2(K_0)$ with class in $N$ such that $P'$ is the pullback of $P$ along $g^{-1}$.
--
--   This is one branch of the forward direction of the local chart-gluing dictionary for the Mumford model: two points of truncated edge charts with the same image in $Z_n$ carry Deligne data differing by an element of the Schottky group $N$, here in the case where the second point lies over the $\xi$-end of its edge. It is cited, together with the companion $\eta$-unit case, in the proof of the dictionary for an arbitrary local ring $B$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_MumfordGlueCore_exists_isPullback_of_zeta_comp_eq_of_isUnit_xi.lean

import Definitions.Def_CerednikDrinfeld_MumfordGlueCore
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_MumfordVertexType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Mumford

theorem CerednikDrinfeld.FormalOmega.MumfordGlueCore.exists_isPullback_of_zeta_comp_eq_of_isUnit_xi
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
    IsUnit (xq' (Ideal.Quotient.mk _ (chartERing.ξ 𝒪 π r))) →
    (∃ g : Matrix.GeneralLinearGroup (Fin 2) K₀, Matrix.ProjGenLinGroup.mk g ∈ N ∧
      (Vertex.act h' (stdVertex 𝒪 K₀) = Vertex.act (g * h) (stdVertex 𝒪 K₀) ∨ Vertex.act h' (stdVertex 𝒪 K₀) = Vertex.act (g * h) (Vertex.act g₁ (stdVertex 𝒪 K₀)))) →
    Spec.map (CommRingCat.ofHom xq.toRingHom) ≫ M.ζ h n = Spec.map (CommRingCat.ofHom xq'.toRingHom) ≫ M.ζ h' n →
      ∃ g : Matrix.GeneralLinearGroup (Fin 2) K₀, Matrix.ProjGenLinGroup.mk g ∈ N ∧ DeligneDatum.IsPullback (K := K₀) (π := π) B g⁻¹ P P' := by sorry
