-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_MumfordGlue_existsUnique_quotientFamily_of_chartLaw
-- name    : CerednikDrinfeld.FormalOmega.MumfordGlue.existsUnique_quotientFamily_of_chartLaw
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/ddf487b6-7f0f-50f6-8e03-1d76849f3eac
-- title:
--   Existence and uniqueness of the chart-law quotient family
-- statement:
--   Fix a prime $r$, a discrete valuation domain $\mathcal O$ with an irreducible element $\pi$ whose residue ring $\mathcal O/(\pi)$ has exactly $r$ elements, and a fraction field $K_0$ of $\mathcal O$; let $g_1\in GL_2(K_0)$ be the matrix $\mathrm{diag}(\pi,1)$, let $N\le PGL(2,K_0)$ be a subgroup, and let `Gl` be a `MumfordGlue` datum for $(\mathcal O,\pi,K_0,r,g_1,N)$, consisting of schemes `Gl.Z n` over $\mathcal O/(\pi^{n+1})$ together with the chart immersions `Gl.ζ h n` and their compatibilities. The assertion is that there is a family $q$ attaching to every $n$, every $\mathcal O$-algebra $B$ with $\pi^{n+1}=0$ in $B$, and every Deligne datum $P$ over $B$ (an object of `Omega K₀ π` at $B$: a family of lines in the base changes of all full lattices, invertible quotients, monotone, homothety-equivariant and nondegenerate at every prime) a morphism $\operatorname{Spec} B \to$ `Gl.Z n`, such that: (i) composing $q\,n\,B\,P$ with `Gl.zb n` and with $\operatorname{Spec}$ of $\mathcal O\to\mathcal O/(\pi^{n+1})$ gives $\operatorname{Spec}$ of the structure map $\mathcal O\to B$; (ii) $q$ is natural, i.e. for an $\mathcal O$-algebra map $\varphi : B\to B'$ between such algebras, $q\,n\,B'\,((\mathrm{Omega}\,K_0\,\pi).\mathrm{map}\,\varphi\,P) = \operatorname{Spec}(\varphi)$ followed by $q\,n\,B\,P$; (iii) the chart law holds: whenever $h\in GL_2(K_0)$, $\bar x$ is an $\mathcal O$-algebra map from `chartERing 𝒪 π r` modulo $(\pi^{n+1})$ to $B$, and $d$ is a Deligne datum over $B$ whose line at the standard full lattice is the $B$-span of $\bar x(\xi)\otimes e_0 + 1\otimes e_1$, whose line at $g_1\cdot(\text{standard lattice})$ is the image under `actBaseChange` of the span of $1\otimes e_0 + \bar x(\eta)\otimes e_1$ (for the distinguished elements `chartERing.ξ 𝒪 π r`, `chartERing.η 𝒪 π r`), and which is edge-nondegenerate at every prime of $B$ for the pair $(g_1\cdot\text{std},\text{std})$, and $P$ is the pullback of $d$ along $h^{-1}$ in the sense that $P.\mathrm{line}\,M$ is the preimage of $d.\mathrm{line}(h^{-1}\cdot M)$ under `actBaseChange` for every full lattice $M$, then $q\,n\,B\,P = \operatorname{Spec}(\bar x)$ followed by `Gl.ζ h n`; and (iv) $q$ is the unique such family, any $q'$ satisfying (ii) and (iii) alone being equal to it.
--
--   This is the representability step in Mumford's construction of the formal scheme uniformising a $p$-adic curve: the glue datum's charts are assembled into a natural transformation from the moduli functor of Deligne data over $\pi$-nilpotent $\mathcal O$-algebras to the points of the schemes `Gl.Z n`, pinned down by its behaviour on chart points and their $GL_2(K_0)$-translates. It is used by [`CerednikDrinfeld.FormalOmega.MumfordGlue.exists_lift_of_valuationRing`](thm.html#CerednikDrinfeld.FormalOmega.MumfordGlue.exists_lift_of_valuationRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_MumfordGlue_existsUnique_quotientFamily_of_chartLaw.lean

import Definitions.Def_CerednikDrinfeld_MumfordGlue
import Definitions.Def_CerednikDrinfeld_MumfordTower
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_MumfordVertexType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Mumford

theorem CerednikDrinfeld.FormalOmega.MumfordGlue.existsUnique_quotientFamily_of_chartLaw
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
    (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])
    (N : Subgroup (PGL(2, K₀)))
    (Gl : MumfordGlue 𝒪 π K₀ r g₁ N) :
    ∃ q : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B], (algebraMap 𝒪 B π) ^ (n + 1) = 0 →
      (Omega K₀ π).obj B → (Spec (CommRingCat.of B) ⟶ Gl.Z n),
      (∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0) (P : (Omega K₀ π).obj B),
    q n B hB P ≫ Gl.zb n ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))) =
      Spec.map (CommRingCat.ofHom (algebraMap 𝒪 B))) ∧
      (∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B']
    (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0) (hB' : (algebraMap 𝒪 B' π) ^ (n + 1) = 0) (φ : B →ₐ[𝒪] B') (P : (Omega K₀ π).obj B),
    q n B' hB' ((Omega K₀ π).map φ P) = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ q n B hB P) ∧
      (∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0)
        (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (xq : ((chartERing 𝒪 π r) ⧸ Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}) →ₐ[𝒪] B) (d P : DeligneDatum (K := K₀) π B),
        (d.line (stdFullLattice K₀) =
            Submodule.span B {((xq.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.ξ 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
          d.line (FullLattice.act g₁ (stdFullLattice K₀)) =
            (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + ((xq.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.η 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
              (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
          d.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) →
        DeligneDatum.IsPullback (K := K₀) (π := π) B h⁻¹ d P →
        q n B hB P = Spec.map (CommRingCat.ofHom xq.toRingHom) ≫ Gl.ζ h n) ∧
      (∀ q' : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B], (algebraMap 𝒪 B π) ^ (n + 1) = 0 →
      (Omega K₀ π).obj B → (Spec (CommRingCat.of B) ⟶ Gl.Z n),
        (∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B']
    (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0) (hB' : (algebraMap 𝒪 B' π) ^ (n + 1) = 0) (φ : B →ₐ[𝒪] B') (P : (Omega K₀ π).obj B),
    q' n B' hB' ((Omega K₀ π).map φ P) = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ q' n B hB P) →
        (∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0)
        (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (xq : ((chartERing 𝒪 π r) ⧸ Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}) →ₐ[𝒪] B) (d P : DeligneDatum (K := K₀) π B),
        (d.line (stdFullLattice K₀) =
            Submodule.span B {((xq.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.ξ 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
          d.line (FullLattice.act g₁ (stdFullLattice K₀)) =
            (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + ((xq.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.η 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
              (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
          d.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) →
        DeligneDatum.IsPullback (K := K₀) (π := π) B h⁻¹ d P →
        q' n B hB P = Spec.map (CommRingCat.ofHom xq.toRingHom) ≫ Gl.ζ h n) → q' = q) := by sorry
