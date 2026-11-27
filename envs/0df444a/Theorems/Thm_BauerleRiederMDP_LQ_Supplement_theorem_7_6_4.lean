-- Prove2me | Theorems.Thm_BauerleRiederMDP_LQ_Supplement_theorem_7_6_4
-- name    : BauerleRiederMDP.LQ.Supplement.theorem_7_6_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T23:59:26.710174+00:00
-- url     : https://prove2.me/theorems/7dbbd399-a172-4f43-871d-82d115427dd4
-- title:
--   Theorem 7.6.4 — fair casino game: value x/B and every stationary strategy that always bets is optimal
-- statement:
--   If $p = 1/2$, then the maximal probability that the player will reach $B$ before going bankrupt is $J_\infty (x) = x/B$, $x \in  E$, and every stationary strategy $(f, f, \dots )$ with $f(x) > 0$ for $x > 0$ is optimal.
--
--   **Formalization Note.** The casino model is the published `MDPFinance.InfiniteHorizonApplications .CasinoMarket` (state space $E = {0, \dots , B}$ as $Fin (B + 1)$, bets $D(x) = {0, \dots , \min (x, B - x)}$, $J_\infty $ the supremum over all Markov policies, $J_f$ the value of $(f, f, \dots )$). $B \in  \mathbb N $ is the book's $B \ge  1$ (for $B = 0$ the formula $x/B$ has no meaning). A rule $f$ is a decision rule, $f(x) \in  D(x)$. Since $D(B) = {0}$, "$f(x) > 0$ for $x > 0$" is required for $0 < x < B$, the states at which a positive bet is feasible.
--
--   Differences from the source:
--   - reading: f(x) > 0 for x > 0 → f(x) > 0 for 0 < x < B, with f(x) ∈ D(x); reason: D(B) = {0}, so a positive bet is feasible only for 0 < x < B
--   - encoding: B ∈ ℕ → 1 ≤ B; reason: for B = 0 the formula x/B has no meaning
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 7.6.4, p.229 (PDF 240)

import Mathlib
import Definitions.Def_MDPFinance_InfiniteHorizonApplications_Casino

open MDPFinance.InfiniteHorizonApplications

namespace BauerleRiederMDP.LQ.Supplement

/-- **Theorem 7.6.4 (fair casino game)** (Bäuerle & Rieder, *Markov Decision Processes with
Applications to Finance* (2011), Theorem 7.6.4, p.229, PDF 240, model of §7.6.3, pp.226–227,
PDF 237–238). If `p = 1/2`, then the maximal probability that the player will reach `B` before going
bankrupt is `J_∞(x) = x/B`, `x ∈ E`, and every stationary strategy `(f, f, …)` with `f(x) > 0` for
`x > 0` is optimal.

**Formalization Note.** The casino model is the published `MDPFinance.InfiniteHorizonApplications
.CasinoMarket` (state space `E = {0, …, B}` as `Fin (B + 1)`, bets `D(x) = {0, …, min(x, B − x)}`,
`J_∞` the supremum over all Markov policies, `J_f` the value of `(f, f, …)`). `B ∈ ℕ` is the book's
`B ≥ 1` (for `B = 0` the formula `x/B` has no meaning). A rule `f` is a decision rule,
`f(x) ∈ D(x)`. Since `D(B) = {0}`, "`f(x) > 0` for `x > 0`" is required for `0 < x < B`, the states
at which a positive bet is feasible. -/
theorem theorem_7_6_4 (Mk : CasinoMarket) (hB : 1 ≤ Mk.B) (hp : Mk.p = 1 / 2) :
    (∀ x : Fin (Mk.B + 1), Mk.Jinf x = (x.1 : ℝ) / Mk.B) ∧
    ∀ f : Fin (Mk.B + 1) → ℕ, (∀ x, f x ∈ Mk.D x) → (∀ x, 0 < x.1 → x.1 < Mk.B → 0 < f x) →
      ∀ x, Mk.Jinfpi f x = Mk.Jinf x := by sorry

end BauerleRiederMDP.LQ.Supplement
