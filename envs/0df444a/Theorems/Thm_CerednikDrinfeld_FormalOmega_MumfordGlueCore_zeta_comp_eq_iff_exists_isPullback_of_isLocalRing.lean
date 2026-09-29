-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_MumfordGlueCore_zeta_comp_eq_iff_exists_isPullback_of_isLocalRing
-- name    : CerednikDrinfeld.FormalOmega.MumfordGlueCore.zeta_comp_eq_iff_exists_isPullback_of_isLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/0f4f8204-a002-58ee-9df1-3f10119fe84a
-- title:
--   Chart points equal iff Deligne data are N-equivalent (local case)
-- statement:
--   Let $\mathcal O$ be a discrete valuation domain with irreducible element $\pi$ whose residue ring $\mathcal O/(\pi)$ has cardinality $r$, a prime, let $K_0$ be a fraction field of $\mathcal O$, let $g_1\in GL_2(K_0)$ be the diagonal matrix $\mathrm{diag}(\pi,1)$, and let $N\le PGL_2(K_0)$ be Schottky for the Bruhat–Tits tree of $(\mathcal O,K_0)$ (trivial vertex stabilisers, no dart sent to its reverse, finitely many vertex and dart orbits) and contained in the subgroup preserving the parity of the distance to the standard vertex. Let $M$ be a Mumford gluing core for these data, with schemes $Z_n$, charts $\zeta_{h,n}\colon \operatorname{Spec}(A_n)\to Z_n$ indexed by $h\in GL_2(K_0)$, where $A_n$ is the edge chart ring $\mathrm{chartERing}\,\mathcal O\,\pi\,r$ modulo $(\pi^{n+1})$. Fix $n$, a local $\mathcal O$-algebra $B$, elements $h,h'\in GL_2(K_0)$, $\mathcal O$-algebra maps $x_q,x_q'\colon A_n\to B$ and Deligne data $d,d',P,P'$ over $B$ (families of $B$-submodules $\mathrm{line}(L)\subseteq B\otimes_{\mathcal O}L$ on full lattices $L$, with invertible quotients, monotone, equivariant under scalar matrices and nondegenerate). Assume $d$ is in standard position for $x_q$: writing $L_0$ for the standard lattice with basis $e_0,e_1$, $d.\mathrm{line}(L_0)$ is spanned by $x_q(\xi)\otimes e_0+1\otimes e_1$, $d.\mathrm{line}(g_1L_0)$ is the image under $\mathrm{actBaseChange}$ of the span of $1\otimes e_0+x_q(\eta)\otimes e_1$, and $d$ satisfies `DeligneDatum.InEdgeChart` for the pair $(g_1L_0,L_0)$, i.e. for every prime $\mathfrak p$ of $B$ one has $g_1L_0\supseteq \pi L_0$, and $1\otimes v\notin \mathrm{line}\oplus\mathfrak p$-part for every $v\in L_0\setminus g_1L_0$, respectively every $v'\in g_1L_0\setminus \pi L_0$; assume the same for $d'$ with $x_q'$. Assume further that $P$ is the pullback of $d$ along $h^{-1}$ and $P'$ the pullback of $d'$ along $h'^{-1}$, in the sense that $P.\mathrm{line}(L)$ is the preimage of $d.\mathrm{line}(h^{-1}L)$ under the base-changed action isomorphism for all full lattices $L$, and likewise for $P'$. Then $\operatorname{Spec}(x_q)$ followed by $\zeta_{h,n}$ equals $\operatorname{Spec}(x_q')$ followed by $\zeta_{h',n}$ if and only if there is $g\in GL_2(K_0)$ whose class in $PGL_2(K_0)$ lies in $N$ such that $P'$ is the pullback of $P$ along $g^{-1}$.
--
--   This is the local dictionary identifying points of the Mumford gluing core with Deligne data up to the Schottky group: over a local base ring, two chart points of the formal model glue to the same point of $Z_n$ exactly when the associated Deligne data differ by an element of $N$. It feeds the chart-relation and overlap law `zeta_rel_and_zeta_overlap`, the unconditional implication `zeta_comp_eq_of_exists_isPullback`, and the Zariski-local covering statement `exists_finite_cover_isPullback_of_zeta_comp_eq`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_MumfordGlueCore_zeta_comp_eq_iff_exists_isPullback_of_isLocalRing.lean

import Definitions.Def_CerednikDrinfeld_MumfordGlueCore
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_MumfordVertexType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.Mumford
open CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.MumfordGlueCore.zeta_comp_eq_iff_exists_isPullback_of_isLocalRing
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
    (Spec.map (CommRingCat.ofHom xq.toRingHom) ≫ M.ζ h n = Spec.map (CommRingCat.ofHom xq'.toRingHom) ≫ M.ζ h' n ↔
      ∃ g : Matrix.GeneralLinearGroup (Fin 2) K₀, Matrix.ProjGenLinGroup.mk g ∈ N ∧ DeligneDatum.IsPullback (K := K₀) (π := π) B g⁻¹ P P') := by sorry
