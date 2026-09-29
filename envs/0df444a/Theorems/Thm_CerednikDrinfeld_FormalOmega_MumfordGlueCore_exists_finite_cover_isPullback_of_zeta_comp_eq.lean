-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_MumfordGlueCore_exists_finite_cover_isPullback_of_zeta_comp_eq
-- name    : CerednikDrinfeld.FormalOmega.MumfordGlueCore.exists_finite_cover_isPullback_of_zeta_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/ebdeff89-ce3f-52ba-bf98-f6a5bc6ee099
-- title:
--   Equal chart points give Zariski-locally N-related Deligne data
-- statement:
--   Let $r$ be a prime, let $\mathcal O$ be a discrete valuation domain with irreducible element $\pi$ whose residue ring $\mathcal O/(\pi)$ has exactly $r$ elements, and let $K_0$ be its fraction field. Let $g_1 \in \mathrm{GL}_2(K_0)$ have matrix $\mathrm{diag}(\pi,1)$, and let $N \le \mathrm{PGL}_2(K_0)$ be a subgroup which is Schottky for the Bruhat–Tits tree of $\mathcal O$ in $K_0$ (all vertex stabilisers trivial, no element sending a dart to its reverse, finitely many orbits of vertices and of darts) and which preserves the type of vertices relative to the standard vertex; and let $M$ be a Mumford gluing core for these data. Then for every $n$, every $\mathcal O$-algebra $B$, all $h,h' \in \mathrm{GL}_2(K_0)$, all $\mathcal O$-algebra maps $x_q, x_q'$ from the edge chart ring $(\mathtt{chartERing}\ \mathcal O\ \pi\ r)/(\pi^{n+1})$ to $B$, and all Deligne data $d, d', P, P'$ over $B$, the following implication holds. Assume $d$ lies in the edge chart at the pair $(g_1 \cdot L_0, L_0)$, $L_0$ the standard full lattice: $d$'s line at $L_0$ is spanned by $x_q(\xi) \otimes e_0 + 1 \otimes e_1$, its line at $g_1 \cdot L_0$ is the image under the base-changed action of $g_1$ of the span of $1 \otimes e_0 + x_q(\eta) \otimes e_1$, and for every prime $\mathfrak p$ of $B$ the edge-nondegeneracy conditions for $g_1 \cdot L_0 \subseteq L_0$ hold for $d$ at $\mathfrak p$; assume the same three conditions for $d'$ with $x_q'$ in place of $x_q$. Assume further that $P$ is obtained from $d$ by pullback along $h^{-1}$, that is, $P$'s line at each full lattice $M$ is the preimage of $d$'s line at $h^{-1} \cdot M$ under the base-changed action of $h^{-1}$, and likewise $P'$ from $d'$ along $h'^{-1}$. Finally assume that $\mathrm{Spec}(x_q)$ followed by $M.\zeta\ h\ n$ equals $\mathrm{Spec}(x_q')$ followed by $M.\zeta\ h'\ n$. Then there are a finite type $\iota$ and $f : \iota \to B$ with $\mathrm{span}(\mathrm{range}\ f) = \top$ such that for each $i$ and each $\mathcal O$-algebra and $B$-algebra $C$, compatibly, which is a localisation of $B$ away from $f(i)$, there is $g \in \mathrm{GL}_2(K_0)$ whose class lies in $N$ with the base change of $P'$ to $C$ equal to the pullback along $g^{-1}$ of the base change of $P$ to $C$.
--
--   This is one half of the dictionary governing Mumford's formal gluing: a coincidence of points in the edge charts of the gluing core forces the corresponding Deligne data to be related by an element of the Schottky group $N$, not over $B$ itself but after passing to a finite Zariski cover of $\mathrm{Spec}\,B$. It is the third conjunct of the chart-relation law [`CerednikDrinfeld.FormalOmega.MumfordGlueCore.zeta_rel_and_zeta_overlap`](thm.html#CerednikDrinfeld.FormalOmega.MumfordGlueCore.zeta_rel_and_zeta_overlap), and is deduced from the local-ring form of the same dictionary by a spreading-out argument over the primes of $B$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_MumfordGlueCore_exists_finite_cover_isPullback_of_zeta_comp_eq.lean

import Definitions.Def_CerednikDrinfeld_MumfordGlueCore
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_MumfordVertexType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Mumford

theorem CerednikDrinfeld.FormalOmega.MumfordGlueCore.exists_finite_cover_isPullback_of_zeta_comp_eq
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
    (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])
    (N : Subgroup (PGL(2, K₀)))
    (hN : IsSchottky (↥N) (BruhatTits.tree 𝒪 K₀))
    (hNtype : N ≤ typePreserving (PGL(2, K₀)) (BruhatTits.tree 𝒪 K₀) (LT.LatticeTree.stdVertex 𝒪 K₀))
    (M : MumfordGlueCore 𝒪 π K₀ r g₁ N) :
    ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B]
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
    Spec.map (CommRingCat.ofHom xq.toRingHom) ≫ M.ζ h n = Spec.map (CommRingCat.ofHom xq'.toRingHom) ≫ M.ζ h' n →
      ∃ (ι : Type) (_ : Finite ι) (f : ι → B), Ideal.span (Set.range f) = ⊤ ∧
        ∀ (i : ι) (C : Type) [CommRing C] [Algebra 𝒪 C] [Algebra B C] [IsScalarTower 𝒪 B C] [IsLocalization.Away (f i) C],
          ∃ g : Matrix.GeneralLinearGroup (Fin 2) K₀, Matrix.ProjGenLinGroup.mk g ∈ N ∧
            DeligneDatum.IsPullback (K := K₀) (π := π) C g⁻¹ ((Omega K₀ π).map (IsScalarTower.toAlgHom 𝒪 B C) P)
              ((Omega K₀ π).map (IsScalarTower.toAlgHom 𝒪 B C) P') := by sorry
