-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_v_period_eq_zpow_neg_sum_stabWidth_mul_pathCycle_mul_pathCycle
-- name    : CerednikDrinfeld.Omega.v_period_eq_zpow_neg_sum_stabWidth_mul_pathCycle_mul_pathCycle
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/f6950e09-834e-56ca-aef4-6d3bc454f0e8
-- title:
--   Stabiliser-weighted Manin–Drinfeld period formula for tree lattices
-- statement:
--   Let $R$ be a discrete valuation domain with fraction field $K_0$, let $\varpi\in R$ be irreducible with finite residue ring $R/(\varpi)$, and let $K$ be a complete field extension of $K_0$ with decidable equality, valued in a linearly ordered commutative group with zero $\Gamma_0$, such that every element of $R$ has valuation $\le 1$ in $K$, every $a\in K_0$ with $v(a)\le 1$ lies in the image of $R$, and the powers $v(\varpi)^N$ are coinitial in $\Gamma_0$. Fix a pseudo-uniformiser $\varpi_1$ for $K_0$ in $K$ (an element of $K_0$ with $0<v<1$ together with the scaling property that every nonzero $a\in K_0$ has $v(\varpi_1)^N\le v(a)\le v(\varpi_1)^{-N}$ for some $N$). Let $G$ be a group, $\rho:G\to \mathrm{PGL}_2(K_0)$ a homomorphism, and let $G$ act on the set of homothety classes of full $R$-lattices in $K_0^2$ preserving adjacency in the Bruhat–Tits tree, the action agreeing with that of $\rho$ ($g\cdot w=\rho(g)\cdot w$), with all vertex stabilisers finite. Let $\tau$ be a $\mathbb{Z}/2$-valued vertex colouring that is $G$-invariant and takes distinct values on adjacent vertices, and let $E$ be a finite type equipped with an equivalence $eE$ onto the set of $G$-orbits of darts $e$ with $\tau(e.\mathrm{out}.\mathrm{fst})=0$. Let $g_0,g_a\in \mathrm{GL}_2(K_0)$ and $w_0,w_a\in K$ lie in the affinoid $\mathrm{affinoid}\ \varpi_1\ 0$, i.e. $v(z)\le 1$ and $v(z-a)\ge 1$ for all $a\in K_0$ with $v(a)\le 1$, and assume $\tau$ separates $g_0\cdot$ and $g_a\cdot$ applied to the standard vertex. Then for all $\alpha,\beta\in G$, writing $a=\mathrm{pmoebius}$ of the class of $g_a$ at $w_a$ and $z_0=\mathrm{pmoebius}$ of the class of $g_0$ at $w_0$, the period $\mathrm{period}\ \rho\ a\ z_0\ \alpha\ \beta$, that is the theta value $\theta(a,\rho(\alpha)a;z_0,\rho(\beta)z_0)$ given by the infinite product over $G$ of the theta factors, has valuation $$v(\varpi)^{-\sum_{e\in E}\,|\mathrm{Stab}_G((eE\,e).\mathrm{out})|\;c_\alpha(e)\,c_\beta(e)},$$ where the weight is $\mathrm{stabWidth}$ of the orbit $(eE\,e)$ and $c_\gamma(e)=\mathrm{pathCycle}$ of $\gamma$ at the standard vertex evaluated at $e$, the signed number of darts of the chosen tree path from the standard vertex to $\gamma$ applied to it lying in the orbit indexed by $e$.
--
--   This is the Manin–Drinfeld period law in the form valid for tree lattices with torsion: the exponent is the intersection pairing of the cycles $c_\alpha,c_\beta$ on the quotient graph, weighted by the orders of the dart stabilisers (Kurihara's edge widths), so that the classical Schottky case is the case of all weights $1$. It feeds the subsequent construction of the period pairing and of the resulting multiplicative lattice data used in the Čerednik–Drinfeld uniformisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_v_period_eq_zpow_neg_sum_stabWidth_mul_pathCycle_mul_pathCycle.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.v_period_eq_zpow_neg_sum_stabWidth_mul_pathCycle_mul_pathCycle
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
    [IsFractionRing R K₀] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a)
    (hq : ∀ ε : Γ₀, ε ≠ 0 → ∃ N : ℕ, Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ N ≤ ε)
    (ϖ₁ : PseudoUniformizer K₀ K)
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀))
    [MulAction G (LT.LatticeTree.Vertex R K₀)]
    [CerednikDrinfeld.Mumford.GraphAction G (CerednikDrinfeld.BruhatTits.tree R K₀)]
    (hρ : CerednikDrinfeld.Mumford.ActsThrough (LT.LatticeTree.Vertex R K₀) ρ)
    (hfin : ∀ w : LT.LatticeTree.Vertex R K₀, Finite (MulAction.stabilizer G w))
    (τ : LT.LatticeTree.Vertex R K₀ → ZMod 2) (hτ : ∀ (g : G) (w : LT.LatticeTree.Vertex R K₀), τ (g • w) = τ w)
    (hadj : ∀ u w : LT.LatticeTree.Vertex R K₀, (CerednikDrinfeld.BruhatTits.tree R K₀).Adj u w → τ u ≠ τ w)
    [DecidableEq (CerednikDrinfeld.Mumford.QuotEdge G (CerednikDrinfeld.BruhatTits.tree R K₀))]
    {E : Type} [Fintype E]
    (eE : E ≃ {e : CerednikDrinfeld.Mumford.QuotEdge G (CerednikDrinfeld.BruhatTits.tree R K₀) // τ e.out.fst = 0})
    (g₀ gₐ : GL (Fin 2) K₀) {w₀ wₐ : K} (hw₀ : w₀ ∈ affinoid ϖ₁ 0) (hwₐ : wₐ ∈ affinoid ϖ₁ 0)
    (hsep : τ (g₀ • LT.LatticeTree.stdVertex R K₀) ≠ τ (gₐ • LT.LatticeTree.stdVertex R K₀))
    (α β : G) :
    Valued.v (period ρ (pmoebius K₀ (Matrix.ProjGenLinGroup.mk gₐ) wₐ) (pmoebius K₀ (Matrix.ProjGenLinGroup.mk g₀) w₀) α β) =
      Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^
        (-(∑ e : E, ((CerednikDrinfeld.Mumford.stabWidth G (CerednikDrinfeld.BruhatTits.tree R K₀) (eE e).1 : ℕ) : ℤ) *
            CerednikDrinfeld.Mumford.pathCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e => (eE e).1)
                (LT.LatticeTree.stdVertex R K₀) α e *
            CerednikDrinfeld.Mumford.pathCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e => (eE e).1)
                (LT.LatticeTree.stdVertex R K₀) β e)) := by sorry
