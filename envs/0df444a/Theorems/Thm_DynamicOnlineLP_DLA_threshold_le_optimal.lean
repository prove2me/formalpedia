-- Prove2me | Theorems.Thm_DynamicOnlineLP_DLA_threshold_le_optimal
-- name    : DynamicOnlineLP.DLA.threshold_le_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T19:35:26.036551+00:00
-- url     : https://prove2.me/theorems/eecb262a-207d-42b7-a0fc-c7df2ae781a5
-- title:
--   Lemma 1 — the threshold solution at an optimal dual price is below every optimal primal solution and differs from it in at most m places
-- statement:
--   Consider the packing linear program with box constraints on a finite column set $S$,
--
--   $$\max\sum_{t\in S}\pi_tx_t\quad\text{s.t.}\quad\sum_{t\in S}a_{it}x_t\le d_i\ (i=1,\dots,m),\quad 0\le x_t\le 1,$$
--
--   and its dual $\min \sum_i d_ip_i+\sum_{t\in S}y_t$ subject to $\sum_i a_{it}p_i+y_t\ge\pi_t$, $p,y\ge0$. Let $x^*$ be an optimal primal solution and $(p^*,y^*)$ an optimal dual solution, and let $x_t(p^*)\in\{0,1\}$ be the threshold rule ($x_t(p^*)=1$ iff $\pi_t>(p^*)^{\top}a_t$). Then
--
--   $$x_t(p^*)\le x^*_t\quad\text{for all }t\in S,$$
--
--   and, if the columns in $S$ are in general position (for any $p\in\mathbb R^m$ at most $m$ columns satisfy $p^{\top}a_t=\pi_t$), then $x_t(p^*)\ne x^*_t$ for at most $m$ indices $t\in S$.
--
--   This is the bridge between dual prices and primal decisions used throughout the paper's analysis: it is applied to the offline LP (1), the sample LP (7) and the partial LP (13).
--
--   **Formalization Note** The paper states the lemma for the offline LP (1); it is stated here for an arbitrary finite column set, arbitrary real data and an arbitrary right-hand side $d$, which covers each LP it is applied to.
-- source:
--   Agrawal, Wang, Ye, A Dynamic Near-Optimal Algorithm for Online Linear Programming, Oper. Res. 62(4), 2014, p. 881, Lemma 1

import Mathlib
import Definitions.Def_DynamicOnlineLP_DLA_PackingLP

namespace DynamicOnlineLP.DLA

/-- Lemma 1 (Agrawal–Wang–Ye 2014, p. 881). Let `x*` be an optimal solution of the packing LP
`max ∑_{t∈S} π_t x_t` s.t. `∑_{t∈S} a_{it} x_t ≤ d_i`, `0 ≤ x_t ≤ 1`, and `(p*, y*)` an optimal
solution of its dual. Then `x_t(p*) ≤ x*_t` for all `t ∈ S`, and under Assumption 3 (general
position) `x*_t` and `x_t(p*)` differ for at most `m` values of `t ∈ S`. -/
theorem threshold_le_optimal {ι : Type} {m : ℕ} (S : Finset ι) (π : ι → ℝ)
    (a : ι → Fin m → ℝ) (d : Fin m → ℝ) (x : ι → ℝ) (p : Fin m → ℝ) (y : ι → ℝ)
    (hx : IsPrimalOptimal S π a d x) (hpy : IsDualOptimal S π a d p y) :
    (∀ t ∈ S, threshold π a p t ≤ x t) ∧
      (GeneralPositionOn S π a → (S.filter (fun t => threshold π a p t ≠ x t)).card ≤ m) := by sorry

end DynamicOnlineLP.DLA
