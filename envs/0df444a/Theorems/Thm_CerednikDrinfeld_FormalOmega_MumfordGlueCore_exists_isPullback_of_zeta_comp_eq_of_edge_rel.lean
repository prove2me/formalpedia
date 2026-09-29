-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_MumfordGlueCore_exists_isPullback_of_zeta_comp_eq_of_edge_rel
-- name    : CerednikDrinfeld.FormalOmega.MumfordGlueCore.exists_isPullback_of_zeta_comp_eq_of_edge_rel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/44e5428b-a293-5e9e-9339-f46f7a9e303a
-- title:
--   Equal chart images on N-equivalent edges give N-related data
-- statement:
--   Fix a prime $r$ and a commutative domain $\mathcal{O}$ assumed to be a discrete valuation ring, with an irreducible element $\pi$ whose residue ring $\mathcal{O}/(\pi)$ has cardinality $r$, and let $K_0$ be a fraction field of $\mathcal{O}$. Let $g_1 \in GL_2(K_0)$ be the matrix $\mathrm{diag}(\pi,1)$, and let $N \le PGL_2(K_0)$ be a subgroup which acts on the Bruhat–Tits tree of $(\mathcal{O},K_0)$ in Schottky fashion (all vertex stabilisers trivial, no dart sent to its reverse, finitely many orbits of vertices and of darts) and which lies in the type-preserving subgroup, i.e. every element of $N$ preserves the parity of the distance to the standard vertex $[\mathcal{O}^2]$. Let $M$ be a Mumford gluing core for the data $(\mathcal{O},\pi,K_0,r,g_1,N)$. The assertion is the following, for every level $n$, every local commutative $\mathcal{O}$-algebra $B$, all $h,h' \in GL_2(K_0)$, all $\mathcal{O}$-algebra maps $x_q,x_q'$ from the truncated edge chart ring $A_n = (\mathrm{chartERing}\ \mathcal{O}\ \pi\ r)/(\pi^{n+1})$ to $B$, and all Deligne data $d,d',P,P'$ over $B$ for $\pi$ and $K_0$. Assume $d$ sits in the standard edge chart with coordinates read off from $x_q$: its line at the standard full lattice $L_0$ is the $B$-span of $x_q(\xi)\otimes e_0 + 1\otimes e_1$, its line at $g_1 L_0$ is the image under the base-changed action of $g_1$ of the span of $1\otimes e_0 + x_q(\eta)\otimes e_1$, and $d$ satisfies the edge chart condition for the pair $(g_1 L_0, L_0)$, namely at every prime ideal $\mathfrak{p}$ of $B$ the corresponding edge nondegeneracy holds; assume the same for $d'$ with $x_q'$ in place of $x_q$. Assume further that $P$ is the pullback of $d$ along $h^{-1}$ and $P'$ the pullback of $d'$ along $h'^{-1}$, in the sense that each line of the former is the comap of the appropriate line of the latter under the base-changed lattice action. Assume finally that the edges $h e_0$ and $h' e_0$ are $N$-equivalent: some $g \in GL_2(K_0)$ has class in $N$ and carries the ordered pair of vertices $(h\,[\mathcal{O}^2], h g_1 [\mathcal{O}^2])$, after multiplication by $h$ on the left and passing to $gh$, to $(h'\,[\mathcal{O}^2], h' g_1 [\mathcal{O}^2])$ either in that order or with the two vertices interchanged. Then, if $\mathrm{Spec}$ of $x_q$ followed by $M.\zeta\ h\ n$ equals $\mathrm{Spec}$ of $x_q'$ followed by $M.\zeta\ h'\ n$, there exists $g \in GL_2(K_0)$ whose class lies in $N$ such that $P'$ is the pullback of $P$ along $g^{-1}$.
--
--   This is one direction of the local dictionary attached to Mumford's chart gluing: two points of the truncated edge charts of a Mumford gluing core have the same image in the scheme $Z_n$ only if the associated Deligne data differ by an element of the Schottky group $N$. It is the case of $N$-equivalent edges, and is used in the proof of [`CerednikDrinfeld.FormalOmega.MumfordGlueCore.exists_isPullback_of_zeta_comp_eq_of_isLocalRing`](thm.html#CerednikDrinfeld.FormalOmega.MumfordGlueCore.exists_isPullback_of_zeta_comp_eq_of_isLocalRing), where the remaining configurations of the two edges are handled separately.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_MumfordGlueCore_exists_isPullback_of_zeta_comp_eq_of_edge_rel.lean

import Definitions.Def_CerednikDrinfeld_MumfordGlueCore
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_MumfordVertexType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Mumford

theorem CerednikDrinfeld.FormalOmega.MumfordGlueCore.exists_isPullback_of_zeta_comp_eq_of_edge_rel
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
    (∃ g : Matrix.GeneralLinearGroup (Fin 2) K₀, Matrix.ProjGenLinGroup.mk g ∈ N ∧
      ((Vertex.act h' (stdVertex 𝒪 K₀) = Vertex.act (g * h) (stdVertex 𝒪 K₀) ∧ Vertex.act h' (Vertex.act g₁ (stdVertex 𝒪 K₀)) = Vertex.act (g * h) (Vertex.act g₁ (stdVertex 𝒪 K₀))) ∨
        (Vertex.act h' (stdVertex 𝒪 K₀) = Vertex.act (g * h) (Vertex.act g₁ (stdVertex 𝒪 K₀)) ∧ Vertex.act h' (Vertex.act g₁ (stdVertex 𝒪 K₀)) = Vertex.act (g * h) (stdVertex 𝒪 K₀)))) →
    Spec.map (CommRingCat.ofHom xq.toRingHom) ≫ M.ζ h n = Spec.map (CommRingCat.ofHom xq'.toRingHom) ≫ M.ζ h' n →
      ∃ g : Matrix.GeneralLinearGroup (Fin 2) K₀, Matrix.ProjGenLinGroup.mk g ∈ N ∧ DeligneDatum.IsPullback (K := K₀) (π := π) B g⁻¹ P P' := by sorry
