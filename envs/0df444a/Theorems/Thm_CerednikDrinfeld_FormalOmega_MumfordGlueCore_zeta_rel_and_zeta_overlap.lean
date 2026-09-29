-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_MumfordGlueCore_zeta_rel_and_zeta_overlap
-- name    : CerednikDrinfeld.FormalOmega.MumfordGlueCore.zeta_rel_and_zeta_overlap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/dddfcdb7-de0c-5d57-9bbe-be32dcb683bc
-- title:
--   Relation and overlap laws for glue core charts
-- statement:
--   Fix a prime $r$, a commutative domain $\mathcal O$ assumed to be a discrete valuation ring, an irreducible $\pi \in \mathcal O$ with $\#(\mathcal O/\pi\mathcal O) = r$, and a fraction field $K_0$ of $\mathcal O$; let $g_1 \in \mathrm{GL}_2(K_0)$ have matrix $\mathrm{diag}(\pi,1)$, and let $N \le \mathrm{PGL}_2(K_0)$ be Schottky for the Bruhat–Tits tree of $(\mathcal O, K_0)$ (trivial vertex stabilisers, no element carrying a dart to its reverse, finitely many vertex and dart orbits) and contained in the subgroup of elements preserving the parity of the tree distance to the standard vertex. Let $M$ be a Mumford glue core for these data, with levels $Z_n$ and charts $\zeta_{h,n} \colon \operatorname{Spec}\bigl((\mathtt{chartERing}\,\mathcal O\,\pi\,r)/(\pi^{n+1})\bigr) \to Z_n$. Three assertions are made, each quantified over $n$, a commutative $\mathcal O$-algebra $B$, elements $h, h' \in \mathrm{GL}_2(K_0)$, $\mathcal O$-algebra maps $xq, xq'$ from $(\mathtt{chartERing}\,\mathcal O\,\pi\,r)/(\pi^{n+1})$ to $B$, and Deligne data $d, d', P, P'$ over $B$ (each assigning to every full lattice $M \subset K_0^2$ a submodule $\mathrm{line}(M) \subseteq B \otimes_{\mathcal O} M$ with invertible quotient, monotone, equivariant under scalar matrices, and nondegenerate at every prime). The common hypotheses are: $d$ has $\mathrm{line}$ at the standard lattice the $B$-span of $xq(\xi) \otimes e_0 + 1 \otimes e_1$ and at $g_1 \cdot$(standard lattice) the image under the base-changed action of the span of $1 \otimes e_0 + xq(\eta) \otimes e_1$, and $d$ is edge-nondegenerate at every prime of $B$ for the pair $(g_1\cdot\text{std}, \text{std})$; the same for $d'$ with $xq'$; and $P$, $P'$ are the $h^{-1}$- and $h'^{-1}$-pullbacks of $d$ and $d'$, meaning $P.\mathrm{line}(M)$ is the preimage of $d.\mathrm{line}(h^{-1}M)$ under the base-changed action, and likewise for $P'$. Under these hypotheses: (i) if there is $g \in \mathrm{GL}_2(K_0)$ with class in $N$ and $P'$ the $g^{-1}$-pullback of $P$, then $\operatorname{Spec}(xq)$ followed by $\zeta_{h,n}$ equals $\operatorname{Spec}(xq')$ followed by $\zeta_{h',n}$; (ii) when $B$ is local, that equality of composites holds if and only if such a $g$ exists; (iii) for general $B$, the equality of composites implies the existence of a finite family $f \colon \iota \to B$ generating the unit ideal such that for each $i$ and each $\mathcal O$-algebra $C$ that is a localisation of $B$ away from $f(i)$ (compatibly with the $\mathcal O$-structures) there is $g \in \mathrm{GL}_2(K_0)$ with class in $N$ for which the image of $P'$ in $C$ is the $g^{-1}$-pullback of the image of $P$.
--
--   This is the verification that the charts of a Mumford glue core satisfy the relation law and the two overlap laws (local and Zariski-local) recognising that two chart points are identified precisely when their associated Deligne data are related by the Schottky group $N$. It packages the three separate chart-comparison results into the form consumed by the construction of a Mumford glue, and is cited in proving that a Mumford glue exists for a type-preserving Schottky group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_MumfordGlueCore_zeta_rel_and_zeta_overlap.lean

import Definitions.Def_CerednikDrinfeld_MumfordGlueCore
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_MumfordVertexType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Mumford

theorem CerednikDrinfeld.FormalOmega.MumfordGlueCore.zeta_rel_and_zeta_overlap
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
    (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])
    (N : Subgroup (PGL(2, K₀)))
    (hN : IsSchottky (↥N) (BruhatTits.tree 𝒪 K₀))
    (hNtype : N ≤ typePreserving (PGL(2, K₀)) (BruhatTits.tree 𝒪 K₀) (LT.LatticeTree.stdVertex 𝒪 K₀))
    (M : MumfordGlueCore 𝒪 π K₀ r g₁ N) :
    (∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B]
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
    (∃ g : Matrix.GeneralLinearGroup (Fin 2) K₀, Matrix.ProjGenLinGroup.mk g ∈ N ∧ DeligneDatum.IsPullback (K := K₀) (π := π) B g⁻¹ P P') →
    Spec.map (CommRingCat.ofHom xq.toRingHom) ≫ M.ζ h n = Spec.map (CommRingCat.ofHom xq'.toRingHom) ≫ M.ζ h' n) ∧
    (∀ (n : ℕ) (B : Type) [CommRing B] [IsLocalRing B] [Algebra 𝒪 B]
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
    (Spec.map (CommRingCat.ofHom xq.toRingHom) ≫ M.ζ h n = Spec.map (CommRingCat.ofHom xq'.toRingHom) ≫ M.ζ h' n ↔
      ∃ g : Matrix.GeneralLinearGroup (Fin 2) K₀, Matrix.ProjGenLinGroup.mk g ∈ N ∧ DeligneDatum.IsPullback (K := K₀) (π := π) B g⁻¹ P P')) ∧
    (∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B]
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
              ((Omega K₀ π).map (IsScalarTower.toAlgHom 𝒪 B C) P')) := by sorry
