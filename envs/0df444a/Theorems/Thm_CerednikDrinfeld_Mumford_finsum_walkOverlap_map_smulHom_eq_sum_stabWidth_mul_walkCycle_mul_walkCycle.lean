-- Prove2me | Theorems.Thm_CerednikDrinfeld_Mumford_finsum_walkOverlap_map_smulHom_eq_sum_stabWidth_mul_walkCycle_mul_walkCycle
-- name    : CerednikDrinfeld.Mumford.finsum_walkOverlap_map_smulHom_eq_sum_stabWidth_mul_walkCycle_mul_walkCycle
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/b6aa2ae5-7d84-5c7b-a074-14e673aae877
-- title:
--   Stabiliser-weighted overlap sum over G-translates of a walk
-- statement:
--   Let $G$ be a group acting on a type $W$ with decidable equality, let $\mathcal T$ be a simple graph on $W$, and assume the action preserves adjacency (so $g$ acts as a graph endomorphism `smulHom g`, sending $w \mapsto g \cdot w$). Assume every vertex stabiliser $\mathrm{Stab}_G(w)$ is finite; assume given $\tau : W \to \mathbb{Z}/2$ with $\tau(g \cdot w) = \tau(w)$ for all $g, w$ and $\tau(u) \neq \tau(v)$ whenever $u$ is adjacent to $v$, i.e. a $G$-invariant proper $2$-colouring. Write $\mathrm{QuotEdge}$ for the set of $G$-orbits of darts of $\mathcal T$ (assumed to have decidable equality), and let $E$ be a finite type equipped with an equivalence $eE$ onto the subtype of those orbits $q$ whose chosen representative $q.\mathrm{out}$ has source of colour $0$. For a walk $p$ and an orbit $q$, $\mathrm{walkCycle}$ assigns to $p$ the integer obtained by summing over the darts $d$ of $p$ the quantity $[\,d \in q\,] - [\,\bar d \in q\,]$, and $\mathrm{stabWidth}\,q$ is $\mathrm{Nat.card}\,\mathrm{Stab}_G(q.\mathrm{out})$ coerced to a positive natural (with $0$ replaced by $1$). Then for any walks $P$ from $u$ to $v$ and $Q$ from $u'$ to $v'$, the $\sum^{\mathrm f}$-sum over all $\gamma \in G$ of the signed overlap $\mathrm{walkOverlap}(P, \gamma \cdot Q)$ — the sum over darts $d$ of $P$ of (multiplicity of $d$ in $\gamma \cdot Q$) minus (multiplicity of $\bar d$ in $\gamma \cdot Q$) — equals $\sum_{e \in E} \mathrm{stabWidth}(eE\,e) \cdot \mathrm{walkCycle}(P)(e) \cdot \mathrm{walkCycle}(Q)(e)$, the orbit indexing being $e \mapsto (eE\,e).1$ on both sides. No tree hypothesis on $\mathcal T$ is imposed.
--
--   This is the finite-stabiliser form of the combinatorial identity underlying the Manin–Drinfeld period law for Mumford curves: a sum over the group of signed dart overlaps is rewritten as a Gram pairing of the images of the two walks in the quotient graph, each oriented quotient edge weighted by the order of the stabiliser of a dart above it (the width). It feeds the valuation computations [`CerednikDrinfeld.Omega.v_period_eq_zpow_neg_sum_stabWidth_mul_pathCycle_mul_pathCycle`](thm.html#CerednikDrinfeld.Omega.v_period_eq_zpow_neg_sum_stabWidth_mul_pathCycle_mul_pathCycle) and [`CerednikDrinfeld.Omega.v_theta_pmoebius_eq_zpow_neg_sum_stabWidth_mul_pathCycle_mul_walkCycle`](thm.html#CerednikDrinfeld.Omega.v_theta_pmoebius_eq_zpow_neg_sum_stabWidth_mul_pathCycle_mul_walkCycle).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Mumford_finsum_walkOverlap_map_smulHom_eq_sum_stabWidth_mul_walkCycle_mul_walkCycle.lean

import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_WalkOverlap
import Mathlib.Algebra.BigOperators.Finprod

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld.Mumford MulAction

theorem CerednikDrinfeld.Mumford.finsum_walkOverlap_map_smulHom_eq_sum_stabWidth_mul_walkCycle_mul_walkCycle
    {G : Type} [Group G] {W : Type} [DecidableEq W] [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
    (hfin : ∀ w : W, Finite (stabilizer G w))
    (τ : W → ZMod 2) (hτ : ∀ (g : G) (w : W), τ (g • w) = τ w) (hadj : ∀ u v : W, 𝒯.Adj u v → τ u ≠ τ v)
    [DecidableEq (QuotEdge G 𝒯)] {E : Type} [Fintype E]
    (eE : E ≃ {e : QuotEdge G 𝒯 // τ e.out.fst = 0})
    {u v u' v' : W} (P : 𝒯.Walk u v) (Q : 𝒯.Walk u' v') :
    ∑ᶠ γ : G, walkOverlap P (Q.map (smulHom γ)) =
      ∑ e : E, ((stabWidth G 𝒯 (eE e).1 : ℕ) : ℤ) *
        (walkCycle 𝒯 (fun e => (eE e).1) P e * walkCycle 𝒯 (fun e => (eE e).1) Q e) := by sorry
