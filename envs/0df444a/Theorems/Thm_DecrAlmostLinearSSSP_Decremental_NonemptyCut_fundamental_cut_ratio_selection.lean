-- Prove2me | Theorems.Thm_DecrAlmostLinearSSSP_Decremental_NonemptyCut_fundamental_cut_ratio_selection
-- name    : DecrAlmostLinearSSSP.Decremental.NonemptyCut.fundamental_cut_ratio_selection
-- status  : Proved
-- author  : @Mr Robbins
-- created : 2026-11-23T03:37:39.085712+00:00
-- url     : https://prove2.me/theorems/8b60990b-d823-4f2a-bb55-0fac43eb5744
-- title:
--   Weighted fundamental-cut decomposition selects a minimum-ratio witness
-- statement:
--   Let $G$ be a finite physical multigraph with nonnegative active capacities, and let $C_0,\ldots,C_{\ell-1}$ be candidate fundamental cuts with nonnegative coefficients $w_i$. Suppose every positively weighted cut has positive capacity, and a direction $x$ admits the exact decompositions
--   $$
--   \gamma\cdot x=\sum_i w_i\gamma(C_i),\qquad
--   \|x\|_u=\sum_i w_i\operatorname{cut}_u(C_i).
--   $$
--   If $\|x\|_u>0$, then some positively weighted $C_i$ has positive capacity and satisfies
--   $$
--   \frac{\gamma(C_i)}{\operatorname{cut}_u(C_i)}
--   \le \frac{\gamma\cdot x}{\|x\|_u}.
--   $$
--
--   Thus an approximate minimum-ratio search over a family of fundamental cuts is sound whenever the family supports such weighted decompositions: optimizing over the directions cannot produce a smaller ratio than optimizing over the cuts. Zero-weight cuts may be empty or disconnected and are ignored. This is the finite weighted-average selection step used at the boundary between a maintained tree decomposition and fundamental-cut ratio selection.
-- source:
--   Cui, Li, Miao and Wang, Partially Dynamic Single-Source Shortest Paths in Almost-Linear Time, STOC 2027 submission #912, p.9, §3.2.1, definition of r* and Lemma 3.2 (adapted from van den Brand et al., Theorem 5.4); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/912.pdf. Exact finite weighted-ratio selection invariant for the tree/fundamental-cut implementation boundary.

import Definitions.Def_DecrAlmostLinearSSSP_TreeCutProtocol

set_option autoImplicit false
open scoped BigOperators ENNReal NNReal

/-- A weighted decomposition of a direction into fundamental cuts has a cut whose
ratio is no larger than the ratio of the direction. -/
theorem DecrAlmostLinearSSSP.Decremental.NonemptyCut.fundamental_cut_ratio_selection {n k ι : ℕ}
    (g : DecrAlmostLinearSSSP.Decremental.Physical n k) (w : Fin ι → ℝ) (C : Fin ι → Finset (Fin n))
    (x : Fin n → ℝ) (hu : ∀ e ∈ g.active, 0 ≤ g.u e)
    (hw : ∀ i, 0 ≤ w i)
    (hpos : ∀ i, 0 < w i → 0 < DecrAlmostLinearSSSP.Decremental.cutCapacity g (C i))
    (hdot : DecrAlmostLinearSSSP.Decremental.dot g.gamma x = ∑ i, w i * DecrAlmostLinearSSSP.Decremental.cutDemand g (C i))
    (hnorm : DecrAlmostLinearSSSP.Decremental.physicalNorm g x = ∑ i, w i * DecrAlmostLinearSSSP.Decremental.cutCapacity g (C i))
    (hnormpos : 0 < DecrAlmostLinearSSSP.Decremental.physicalNorm g x) :
    ∃ i, 0 < w i ∧ 0 < DecrAlmostLinearSSSP.Decremental.cutCapacity g (C i) ∧
      DecrAlmostLinearSSSP.Decremental.cutDemand g (C i) / DecrAlmostLinearSSSP.Decremental.cutCapacity g (C i) ≤
        DecrAlmostLinearSSSP.Decremental.dot g.gamma x / DecrAlmostLinearSSSP.Decremental.physicalNorm g x := by sorry
