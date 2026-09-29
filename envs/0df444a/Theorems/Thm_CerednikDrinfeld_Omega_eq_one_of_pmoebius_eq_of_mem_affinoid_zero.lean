-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_eq_one_of_pmoebius_eq_of_mem_affinoid_zero
-- name    : CerednikDrinfeld.Omega.eq_one_of_pmoebius_eq_of_mem_affinoid_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/ccd391ce-b18c-5f3e-bb14-7882d61dbf71
-- title:
--   Schottky groups act freely on the affinoid g·Ω₀
-- statement:
--   Let $R$ be a discrete valuation domain with fraction field $K_0$ and let $\varpi \in R$ be irreducible. Let $K$ be a field extension of $K_0$, equipped with decidable equality and with a valuation taking values in a linearly ordered commutative group with zero $\Gamma_0$, subject to two compatibility hypotheses: the image in $K$ of every element of $R$ has valuation at most $1$, and every $a \in K_0$ whose image in $K$ has valuation at most $1$ is an integer of $R$ (i.e. lies in the image of $R$). Let $\varpi_1$ be a pseudo-uniformizer, that is an element of $K_0$ whose image in $K$ has valuation strictly between $0$ and $1$ and such that every nonzero $a \in K_0$ satisfies $\mathfrak{p}^N \le v(a) \le \mathfrak{p}^{-N}$ for some $N \in \mathbb{N}$, where $\mathfrak{p}$ denotes the valuation of the image of $\varpi_1$. Let $G$ be a group acting on the set of homothety classes of full $R$-lattices in $K_0^2$, the action preserving adjacency in the Bruhat–Tits tree, let $\rho : G \to \mathrm{PGL}_2(K_0)$ be a homomorphism through which the action factors ($\gamma \cdot v = \rho(\gamma)\cdot v$ for all $\gamma$ and all vertices $v$), and assume `IsSchottky` holds for this action: all vertex stabilisers are trivial, no group element sends a dart to its reverse, and there are finitely many vertex orbits and finitely many dart orbits. Finally let $g \in \mathrm{GL}_2(K_0)$, let $w, w'$ lie in the level-$0$ affinoid $\{z \in K : v(z) \le 1 \text{ and } v(z - a) \ge 1 \text{ for all } a \in K_0 \text{ with } v(a) \le 1\}$, and let $\gamma \in G$ satisfy $\rho(\gamma) \cdot (g \cdot w) = g \cdot w'$, the dot denoting the fractional linear action of $\mathrm{PGL}_2(K_0)$ on $K$ (with $\infty$ sent to $0$). Then $\gamma = 1$ and $w = w'$.
--
--   This is the freeness statement for a $p$-adic Schottky group acting on the fibres of the reduction map from the Drinfeld upper half plane to the Bruhat–Tits tree: distinct points of the translated standard affinoid $g\cdot\Omega_0$ are never identified by the group, and only the identity stabilises such a point. It supplies the 'point not in the orbit of another' guards used in the construction of Manin–Drinfeld theta functions and periods, and is cited in the identification of principal divisor classes with periods on the resulting curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_eq_one_of_pmoebius_eq_of_mem_affinoid_zero.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.eq_one_of_pmoebius_eq_of_mem_affinoid_zero
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
    [IsFractionRing R K₀] (ϖ : R) (hϖ : Irreducible ϖ)
    (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a)
    (ϖ₁ : PseudoUniformizer K₀ K)
    {G : Type} [Group G] [MulAction G (LT.LatticeTree.Vertex R K₀)]
    [CerednikDrinfeld.Mumford.GraphAction G (CerednikDrinfeld.BruhatTits.tree R K₀)]
    (ρ : G →* PGL(2, K₀)) (hρ : CerednikDrinfeld.Mumford.ActsThrough (LT.LatticeTree.Vertex R K₀) ρ)
    (hS : CerednikDrinfeld.Mumford.IsSchottky G (CerednikDrinfeld.BruhatTits.tree R K₀))
    (g : GL (Fin 2) K₀) {w w' : K} (hw : w ∈ affinoid ϖ₁ 0) (hw' : w' ∈ affinoid ϖ₁ 0) (γ : G)
    (h : pmoebius K₀ (ρ γ) (pmoebius K₀ (Matrix.ProjGenLinGroup.mk g) w) =
           pmoebius K₀ (Matrix.ProjGenLinGroup.mk g) w') :
    γ = 1 ∧ w = w' := by sorry
