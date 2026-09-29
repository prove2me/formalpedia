-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_MumfordGlueCore_exists_isPullback_of_zeta_comp_eq_of_isLocalRing
-- name    : CerednikDrinfeld.FormalOmega.MumfordGlueCore.exists_isPullback_of_zeta_comp_eq_of_isLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/4d583767-e630-579c-b57e-8c25568d1ae5
-- title:
--   Equal chart points over a local base give N-related Deligne data
-- statement:
--   Let $r$ be a prime, $\mathcal O$ a discrete valuation domain with irreducible element $\pi$ whose residue ring $\mathcal O/(\pi)$ has cardinality $r$, and $K_0$ a fraction field of $\mathcal O$; let $g_1\in GL_2(K_0)$ be the diagonal matrix $\mathrm{diag}(\pi,1)$, and let $N\le PGL_2(K_0)$ be a subgroup which is Schottky for the Bruhat–Tits tree of $\mathcal O$ in $K_0$ (trivial vertex stabilisers, no element inverting a dart, finitely many vertex and dart orbits) and type-preserving with respect to the standard vertex, i.e. contained in the subgroup of elements preserving the parity of the distance to the standard vertex. Let $M$ be a `MumfordGlueCore` for $(\mathcal O,\pi,K_0,r,g_1,N)$. Fix $n\in\mathbb N$, a local $\mathcal O$-algebra $B$, elements $h,h'\in GL_2(K_0)$, two $\mathcal O$-algebra maps $x_q,x_q'$ from the edge chart ring `chartERing 𝒪 π r` modulo $\pi^{n+1}$ to $B$, and four Deligne data $d,d',P,P'$ over $B$ for $(\pi,K_0)$. Assume $d$ is in standard edge position for $x_q$: its line at the standard full lattice is spanned by $x_q(\xi)\otimes e_0+1\otimes e_1$, its line at $g_1\cdot(\text{standard lattice})$ is the image under the base-changed action of $g_1$ of the span of $1\otimes e_0+x_q(\eta)\otimes e_1$, and $d$ lies in the edge chart for the pair $(g_1\cdot\text{std},\text{std})$, meaning that at every prime $\mathfrak p$ of $B$ the inclusion and $\pi$-divisibility conditions hold and the classes $1\otimes v$ of vectors of the larger lattice outside the smaller one, and of vectors of the smaller one not divisible by $\pi$, avoid the relevant line plus $\mathfrak p\cdot\top$; assume the same three conditions for $d'$ with $x_q'$. Assume $P$ is the pullback of $d$ along $h^{-1}$ and $P'$ the pullback of $d'$ along $h'^{-1}$, that is, $P.\mathrm{line}\,M=(d.\mathrm{line}(h^{-1}\cdot M))$ pulled back along the base-changed action of $h^{-1}$ for every full lattice $M$, and likewise for $P'$. Finally assume that $\mathrm{Spec}(x_q)$ followed by $\zeta_{h,n}$ equals $\mathrm{Spec}(x_q')$ followed by $\zeta_{h',n}$ in schemes. Then there exists $g\in GL_2(K_0)$ whose class in $PGL_2(K_0)$ lies in $N$ such that $P'$ is the pullback of $P$ along $g^{-1}$.
--
--   This is one direction of the local chart-gluing dictionary for the Mumford-style gluing data underlying the Čerednik–Drinfeld uniformisation: two points of edge charts, with values in a local $\mathcal O$-algebra, that have the same image in the glued scheme $Z_n$ carry Deligne data differing by an element of the Schottky group $N$. It is used, together with its converse, to prove the equivalence `zeta_comp_eq_iff_exists_isPullback_of_isLocalRing`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_MumfordGlueCore_exists_isPullback_of_zeta_comp_eq_of_isLocalRing.lean

import Definitions.Def_CerednikDrinfeld_MumfordGlueCore
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_MumfordVertexType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Mumford

theorem CerednikDrinfeld.FormalOmega.MumfordGlueCore.exists_isPullback_of_zeta_comp_eq_of_isLocalRing
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
    Spec.map (CommRingCat.ofHom xq.toRingHom) ≫ M.ζ h n = Spec.map (CommRingCat.ofHom xq'.toRingHom) ≫ M.ζ h' n →
      ∃ g : Matrix.GeneralLinearGroup (Fin 2) K₀, Matrix.ProjGenLinGroup.mk g ∈ N ∧ DeligneDatum.IsPullback (K := K₀) (π := π) B g⁻¹ P P' := by sorry
