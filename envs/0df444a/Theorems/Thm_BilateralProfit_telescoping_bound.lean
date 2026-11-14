-- Prove2me | Theorems.Thm_BilateralProfit_telescoping_bound
-- name    : BilateralProfit.telescoping_bound
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T02:22:06.178147+00:00
-- url     : https://prove2.me/theorems/ff2257f2-7cbe-4ec0-9bd1-1f9ba13d9c78
-- title:
--   §4.2.2 (proof of Theorem 4.1) — telescoping regret bound on the grid
-- statement:
--   Let $K\ge1$ and let $C_0$ be a constant for which the information inequality of Theorem 4.2 holds at resolution $K$. Run Algorithm 1 on a valuation sequence $v_1,\dots,v_T\in G_K$. Then:
--
--   1. every weight vector $w_1,\dots,w_{T+1}$ of every run is a probability vector with entries at least $1/(|\mathcal A|(1+\beta K))$ (the lower-bound condition of Lemma 4.6 holds initially and is preserved by each update (5));
--   2. for every comparison price $a'\in\mathcal A$,
--   $$\sum_{t=1}^T\mathrm{Profit}(v_t,a')-\mathbb E\Big[\sum_{t=1}^T\mathrm{Profit}(v_t,a_t)\Big]\le\frac{(C_0+2)T}K+\beta\,\mathbb E\Big[\log\frac{w_{T+1}(a')}{w_1(a')}\Big]\le\frac{(C_0+2)T}K+\beta\log|\mathcal A| .$$
--
--   Together with grid rounding and Lemma A.6 this gives the regret bound of Theorem 4.1.
--
--   **Formalization Note** The expectation is the average over the $J^T$ draw sequences; $w_{t+1}$ is the weight vector at index $t$.
--
--   Differences from the source:
--   - generalization: $C_0$ the universal constant of Theorem 4.2 → any $C_0$ for which Theorem 4.2's inequality holds at this $K$ for every $\rho$; reason: the universal $C_0$ is such a constant
--   - encoding: the grid $G_K$ of step size $1/K$ → hypothesis $0<K$; reason: the step size $1/K$ presupposes $K\ge1$ (Lemma A.6: "for every integer $K\ge1$")
--   - reading: the displayed chain (p.23), preceded by "The lower-bound condition on $w_t$ of Lemma 4.6 holds initially and is preserved by each update prescribed as in Equation (5)" (p.22) → both as clauses: every $w_1,\dots,w_{T+1}$ of every run is a probability vector with entries $\ge1/(|\mathcal A|(1+\beta K))$, and the chain; reason: the chain's proof rests on the invariant the page asserts, and stating it keeps Lemma 4.6's hypothesis from being vacuous along the run
--   - encoding: the expectation over the learner's randomness; rounds $1,\dots,T$ → the uniform average over draw sequences $\omega:\{0,\dots,T-1\}\to\{0,\dots,J-1\}$; $w_{t+1}$ at index $t$; reason: Algorithm 1's only randomness is the independent uniform $j^\star$ of each OneRound call
-- source:
--   Brüstle, di Gregorio, Fusco, Leonardi, Regret Bounds for Profit Maximization in Bilateral Trade: Learning the Best Posted-Price Mechanism (manuscript, STOC 2027 submission, sha256 e91e81279505b765c7c96c219d674c0fbbbd6ca47a00da8fe228d498ca25ac87), proof of Theorem 4.1, §4.2.2, pp.22–23 (PDF 24–25)

import Mathlib
import Definitions.Def_BilateralProfit_Algorithm1

namespace BilateralProfit

/-- **The telescoping bound in the proof of Theorem 4.1**, Brüstle, di Gregorio, Fusco, Leonardi
(manuscript, sha256 e91e8127…), §4.2.2, pp.22–23 (PDF 24–25).

Let `C0` be a constant for which the information inequality (Theorem 4.2) holds at resolution
`K`, and run Algorithm 1 on a valuation sequence `v_1, …, v_T ∈ G_K`. Then
1. every weight vector `w_1, …, w_{T+1}` of every run is a probability vector with entries at least
   `1/(|𝒜|(1 + βK))` (the lower-bound condition of Lemma 4.6 "holds initially and is preserved by
   each update prescribed as in Equation (5)");
2. for every comparison price `a′ ∈ 𝒜`,
   `Σ_t Profit(v_t, a′) − E[Σ_t Profit(v_t, a_t)] ≤ (C0 + 2)T/K + β E[log(w_{T+1}(a′)/w_1(a′))]
     ≤ (C0 + 2)T/K + β log|𝒜|`.

**Formalization Note.** `w_{t+1}` is `alg1W … t` (`t = 0, …, T`); the expectation is over the
uniform draws `ω`. -/
theorem telescoping_bound (K : ℕ) (hK : 0 < K) (C₀ : ℝ)
    (hC₀ : ∀ ρ : Grid K × Act K → ℝ, IsDist ρ →
      ∃ a : Act K, gap ρ a - beta K * info ρ a ≤ C₀ / K)
    (T : ℕ) (v : Fin T → Grid K) :
    (∀ ω : Fin T → Fin (Jpar K), ∀ t, t ≤ T →
      IsDist (alg1W K T (fun s => pt K (v s)) ω t) ∧
        ∀ a', wFloor K ≤ alg1W K T (fun s => pt K (v s)) ω t a') ∧
    ∀ a' : Act K,
      ∑ t, profit (pt K (v t)) (pt K a'.1) -
          expectAlg K T (fun ω => ∑ t, profit (pt K (v t))
            (pt K (alg1Act K T (fun s => pt K (v s)) ω t).1)) ≤
        (C₀ + 2) * T / K + beta K * expectAlg K T (fun ω =>
          Real.log (alg1W K T (fun s => pt K (v s)) ω T a' /
            alg1W K T (fun s => pt K (v s)) ω 0 a')) ∧
      (C₀ + 2) * T / K + beta K * expectAlg K T (fun ω =>
          Real.log (alg1W K T (fun s => pt K (v s)) ω T a' /
            alg1W K T (fun s => pt K (v s)) ω 0 a')) ≤
        (C₀ + 2) * T / K + beta K * Real.log (nA K) := by sorry

end BilateralProfit
