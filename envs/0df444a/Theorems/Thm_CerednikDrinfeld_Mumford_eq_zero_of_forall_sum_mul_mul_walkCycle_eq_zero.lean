-- Prove2me | Theorems.Thm_CerednikDrinfeld_Mumford_eq_zero_of_forall_sum_mul_mul_walkCycle_eq_zero
-- name    : CerednikDrinfeld.Mumford.eq_zero_of_forall_sum_mul_mul_walkCycle_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/4d2b4d37-f6e5-563e-b681-a175a659e377
-- title:
--   Uniqueness of weighted dart-orbit cochains on the Bruhat–Tits tree
-- statement:
--   Let $R$ be a discrete valuation domain with fraction field $K_0$, and let [`CerednikDrinfeld.BruhatTits.tree R K₀`](def/CerednikDrinfeld_BruhatTitsTree.html#L83) be the graph on [`LT.LatticeTree.Vertex R K₀`](def/LatticeTreeOrbital.html#L349), the homothety classes of full $R$-lattices in $K_0^2$, obtained from the relation that two classes have adjacent lattice representatives. Let $G$ be a group acting on the vertex set so that adjacency is preserved, let $\tau$ be a $\mathbb{Z}/2$-valued function on vertices that is $G$-invariant ($\tau(g\cdot w)=\tau(w)$) and takes distinct values on adjacent vertices, i.e. a $G$-invariant proper $2$-colouring. Let $E$ be a finite type together with a bijection `eE` onto those orbits $q$ of $G$ on the darts of the tree whose chosen representative `q.out` has source of colour $0$. Let $w,d\colon E\to\mathbb{Z}$ with $w$ nowhere zero. Assume that for every $g\in\mathrm{GL}_2(K_0)$ and every walk $p$ in the tree from the standard vertex (the class of the lattice of integral vectors) to $g$ times the standard vertex one has $\sum_{e} w(e)\,d(e)\,[p](e)=0$, where $[p](e)$ is the sum over the darts of $p$ of the index $+1$ for darts in the orbit `(eE e).1`, $-1$ for darts whose reversal lies in that orbit, and $0$ otherwise. Then $d=0$.
--
--   This is the uniqueness statement for weighted integral currents (edge cochains) on the quotient of the Bruhat–Tits tree by a group acting with a preserved two-colouring: a weighted cochain annihilating all walk classes from the standard vertex vanishes. It is used in the construction of Mumford-type periods, in [`CerednikDrinfeld.Omega.exists_forall_eq_period_of_isUnit_of_apply_smul_eq_mul_of_forall_isOfFinOrder`](thm.html#CerednikDrinfeld.Omega.exists_forall_eq_period_of_isUnit_of_apply_smul_eq_mul_of_forall_isOfFinOrder).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Mumford_eq_zero_of_forall_sum_mul_mul_walkCycle_eq_zero.lean

import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.Mumford MulAction

theorem CerednikDrinfeld.Mumford.eq_zero_of_forall_sum_mul_mul_walkCycle_eq_zero
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    {G : Type} [Group G] [MulAction G (LT.LatticeTree.Vertex R K₀)]
    [GraphAction G (CerednikDrinfeld.BruhatTits.tree R K₀)]
    (τ : LT.LatticeTree.Vertex R K₀ → ZMod 2) (hτ : ∀ (g : G) (w : LT.LatticeTree.Vertex R K₀), τ (g • w) = τ w)
    (hadj : ∀ u w : LT.LatticeTree.Vertex R K₀, (CerednikDrinfeld.BruhatTits.tree R K₀).Adj u w → τ u ≠ τ w)
    [DecidableEq (QuotEdge G (CerednikDrinfeld.BruhatTits.tree R K₀))]
    {E : Type} [Fintype E] (eE : E ≃ {e : QuotEdge G (CerednikDrinfeld.BruhatTits.tree R K₀) // τ e.out.fst = 0})
    (w : E → ℤ) (hw : ∀ e : E, w e ≠ 0)
    (d : E → ℤ)
    (h : ∀ (g : GL (Fin 2) K₀)
      (p : (CerednikDrinfeld.BruhatTits.tree R K₀).Walk (LT.LatticeTree.stdVertex R K₀) (g • LT.LatticeTree.stdVertex R K₀)),
      ∑ e, w e * d e * walkCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e => (eE e).1) p e = 0) :
    d = 0 := by sorry
