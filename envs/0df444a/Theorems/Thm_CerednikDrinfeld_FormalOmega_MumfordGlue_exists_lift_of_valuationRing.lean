-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_MumfordGlue_exists_lift_of_valuationRing
-- name    : CerednikDrinfeld.FormalOmega.MumfordGlue.exists_lift_of_valuationRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/2105116f-e466-58fe-b3e3-8c9121f1e7e4
-- title:
--   Valuative lifting of points of the glued Mumford levels
-- statement:
--   Let $r$ be a prime, let $\mathcal O$ be a discrete valuation domain with an irreducible element $\pi$ such that $\mathcal O/(\pi)$ has exactly $r$ elements, and let $K_0$ be a fraction field of $\mathcal O$. Fix $g_1 \in \mathrm{GL}_2(K_0)$ whose matrix is $\mathrm{diag}(\pi,1)$, a subgroup $N \le \mathrm{PGL}_2(K_0)$, and a datum $Gl$ of type `MumfordGlue 𝒪 π K₀ r g₁ N`: schemes $Z_n$ with structure morphisms $zb_n : Z_n \to \operatorname{Spec}(\mathcal O/\pi^{n+1})$, transition maps $zt_n : Z_n \to Z_{n+1}$ making each square over $\mathcal O/\pi^{n+2} \to \mathcal O/\pi^{n+1}$ a pullback, each $zb_n$ flat and separated, together with charts $\zeta_{h,n}$ from $\operatorname{Spec}$ of the edge chart ring modulo $\pi^{n+1}$, indexed by $h \in \mathrm{GL}_2(K_0)$, which are open immersions lying over $\mathcal O$, compatible with the transition maps, covering $Z_n$ by finitely many of them, invariant under left translation by elements of $N$, and subject to the relation law `ζ_rel` describing overlaps in terms of Deligne data. Let $n \in \mathbb N$, let $V$ be a valuation domain with fraction field $L$, and let $y : \operatorname{Spec} L \to Z_n$ and $b : \operatorname{Spec} V \to \operatorname{Spec}(\mathcal O/\pi^{n+1})$ satisfy: the map $\operatorname{Spec} L \to \operatorname{Spec} V$ followed by $b$ equals $y$ followed by $zb_n$. Then there is $y_V : \operatorname{Spec} V \to Z_n$ with $\operatorname{Spec} L \to \operatorname{Spec} V$ followed by $y_V$ equal to $y$, and $y_V$ followed by $zb_n$ equal to $b$.
--
--   This is the existence half of the valuative criterion of properness for the structure morphisms $zb_n$ of the glued Mumford levels, stated for arbitrary valuation rings rather than only discrete ones. It is used in the proof that each $zb_n$ is proper.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_MumfordGlue_exists_lift_of_valuationRing.lean

import Definitions.Def_CerednikDrinfeld_MumfordGlue

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.MumfordGlue.exists_lift_of_valuationRing
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
    (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])
    (N : Subgroup (PGL(2, K₀)))
    (Gl : MumfordGlue 𝒪 π K₀ r g₁ N)
    (n : ℕ) (V : Type) [CommRing V] [IsDomain V] [ValuationRing V]
    (L : Type) [Field L] [Algebra V L] [IsFractionRing V L]
    (y : Spec (CommRingCat.of L) ⟶ Gl.Z n) (b : Spec (CommRingCat.of V) ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))
    (hsq : Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ b = y ≫ Gl.zb n) :
    ∃ yV : Spec (CommRingCat.of V) ⟶ Gl.Z n, Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ yV = y ∧ yV ≫ Gl.zb n = b := by sorry
