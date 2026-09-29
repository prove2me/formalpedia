-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_MumfordGlueCore_zeta_comp_eq_of_exists_isPullback
-- name    : CerednikDrinfeld.FormalOmega.MumfordGlueCore.zeta_comp_eq_of_exists_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/cda834e8-61ae-5104-a902-60ae61c80084
-- title:
--   N-related Deligne data give the same chart point
-- statement:
--   Fix a prime $r$ and a domain $\mathcal{O}$ that is a discrete valuation ring, with $\pi \in \mathcal{O}$ irreducible and residue ring $\mathcal{O}/(\pi)$ of cardinality $r$, and let $K_0$ be its fraction field. Let $g_1 \in \mathrm{GL}_2(K_0)$ have matrix $\mathrm{diag}(\pi,1)$, and let $N \le \mathrm{PGL}_2(K_0)$ satisfy `IsSchottky` for the Bruhat–Tits tree of $\mathcal{O}$ in $K_0$ (all vertex stabilisers in $N$ trivial, no dart sent to its reverse, finitely many $N$-orbits of vertices and of darts) and be contained in the subgroup preserving the parity of the distance to the standard vertex; let $M$ be a `MumfordGlueCore` for these data. Then for every $n$, every $\mathcal{O}$-algebra $B$, all $h,h' \in \mathrm{GL}_2(K_0)$, all $\mathcal{O}$-algebra maps $x_q, x_q'$ from the edge chart ring `chartERing` $\mathcal{O}\,\pi\,r$ modulo $\pi^{n+1}$ to $B$, and all Deligne data $d,d',P,P'$ over $B$ the following holds. Assume $d$ lies in the edge chart cut out by $x_q$: its line at the standard lattice $L_0$ is spanned by $x_q(\xi) \otimes e_0 + 1 \otimes e_1$, its line at $g_1 L_0$ is the image under the base-changed action of $g_1$ of the span of $1 \otimes e_0 + x_q(\eta) \otimes e_1$, and $d$ satisfies `InEdgeChart` for the pair $(g_1 L_0, L_0)$, that is, for every prime ideal of $B$ the corresponding edge-nondegeneracy conditions hold; assume the same for $d'$ with $x_q'$. Assume further that $P$ is the $h^{-1}$-pullback of $d$ and $P'$ the $h'^{-1}$-pullback of $d'$, in the sense that each line of $P$ (resp. $P'$) is the preimage of the line of $d$ (resp. $d'$) at the translated lattice, and that there exists $g \in \mathrm{GL}_2(K_0)$ whose class lies in $N$ with $P'$ the $g^{-1}$-pullback of $P$. Then $\mathrm{Spec}\,x_q$ followed by $M.\zeta\,h\,n$ equals $\mathrm{Spec}\,x_q'$ followed by $M.\zeta\,h'\,n$ as morphisms $\mathrm{Spec}\,B \to M.Z\,n$.
--
--   This is the gluing compatibility for Mumford's construction: Deligne data identified by an element of the Schottky group $N$ define the same point of the $n$-th layer of the glued formal scheme, whatever the $\mathcal{O}$-algebra $B$. It is the unconditional half of the chart-relation law `zeta_rel_and_zeta_overlap`, obtained from the local-ring version `zeta_comp_eq_iff_exists_isPullback_of_isLocalRing` by testing morphisms out of $\mathrm{Spec}\,B$ on the localisations at all primes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_MumfordGlueCore_zeta_comp_eq_of_exists_isPullback.lean

import Definitions.Def_CerednikDrinfeld_MumfordGlueCore
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_MumfordVertexType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Mumford

theorem CerednikDrinfeld.FormalOmega.MumfordGlueCore.zeta_comp_eq_of_exists_isPullback
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
    (∃ g : Matrix.GeneralLinearGroup (Fin 2) K₀, Matrix.ProjGenLinGroup.mk g ∈ N ∧ DeligneDatum.IsPullback (K := K₀) (π := π) B g⁻¹ P P') →
    Spec.map (CommRingCat.ofHom xq.toRingHom) ≫ M.ζ h n = Spec.map (CommRingCat.ofHom xq'.toRingHom) ≫ M.ζ h' n := by sorry
