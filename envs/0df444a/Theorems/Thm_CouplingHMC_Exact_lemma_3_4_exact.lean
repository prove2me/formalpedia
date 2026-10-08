-- Prove2me | Theorems.Thm_CouplingHMC_Exact_lemma_3_4_exact
-- name    : CouplingHMC.Exact.lemma_3_4_exact
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T05:27:30.664603+00:00
-- url     : https://prove2.me/theorems/9ba8fb45-b3d4-468b-b329-6204a66c2189
-- title:
--   Lemma 3.4, case h = 0, p. 21 — |q_t(x,v) − q_t(y,v)|² ≤ (1 − Kt²/2)|x − y|² for |x − y| ≥ 2ℛ and Lt² < K/L
-- statement:
--   Suppose Assumption 2.1 holds and let $(q_t,p_t)$ be the exact Hamiltonian flow of $H(x,v)=U(x)+\tfrac12|v|^2$. Let $t\ge0$ with $Lt^2\le1$ and $Lt^2<K/L$. Then for all $x,y,v\in\mathbb R^d$ with $|x-y|\ge2\mathcal R$,
--
--   $$|q_t(x,v)-q_t(y,v)|^2\le\Bigl(1-\frac{Kt^2}{2}\Bigr)|x-y|^2.$$
--
--   Two Hamiltonian trajectories started with the same velocity from points at distance at least $2\mathcal R$ approach each other: this is where the strong convexity of $U$ outside a ball enters.
--
--   **Formalization Note.** This is the case $h=0$ (exact flow) of the paper's lemma. There the condition $(1+|x|+|v|)h\le K/C$ of (57) reads $0\le K/C$ and holds for every $C>0$, so the constant $C$ disappears. The hypothesis $Lt^2\le1$ is the standing assumption (46) of §3.1 at $h=0$. In Lean, the strict condition is $L^2t^2<K$: it is equivalent to $Lt^2<K/L$ when $L>0$ and retains the intended case $L=0$.
-- source:
--   Bou-Rabee, Eberle, Zimmer, Coupling and convergence for Hamiltonian Monte Carlo, arXiv:1805.00452v2, Lemma 3.4, (55)–(57), with (46), pp. 20–21

import Mathlib
import Definitions.Def_CouplingHMC_Exact_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace

namespace CouplingHMC.Exact

/-- Lemma 3.4 (p. 21), case `h = 0`: for the exact flow, `t ≥ 0` with `Lt² ≤ 1` ((46)) and
`Lt² < K/L` ((56)), and `|x - y| ≥ 2ℛ`, `|q_t(x, v) - q_t(y, v)|² ≤ (1 - Kt²/2)|x - y|²`.
The strict condition is written `L²t² < K`, equivalent for `L > 0` and also valid at `L = 0`. -/
theorem lemma_3_4_exact {d : ℕ} (U : E d → ℝ) (L M N ℛ K : ℝ) (hU : Assumption21 U L M N ℛ K)
    (q p : ℝ → E d → E d → E d) (hflow : IsExactFlow U q p) (t : ℝ) (ht : 0 ≤ t)
    (h46 : L * t ^ 2 ≤ 1) (h56 : L ^ 2 * t ^ 2 < K) (x y v : E d) (hxy : 2 * ℛ ≤ ‖x - y‖) :
    ‖q t x v - q t y v‖ ^ 2 ≤ (1 - K * t ^ 2 / 2) * ‖x - y‖ ^ 2 := by sorry

end CouplingHMC.Exact
