-- Prove2me | Theorems.Thm_BauerleRiederMDP_TransactionCosts_eq_4_33
-- name    : BauerleRiederMDP.TransactionCosts.eq_4_33
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:31:47.60727+00:00
-- url     : https://prove2.me/theorems/87a10c1d-a15c-42eb-86c7-23c55bc779b0
-- title:
--   (4.33) — stock-to-bond ratio after transaction under the optimal policy
-- statement:
--   Under the standing assumptions of §4.5, let $f^*_n$ be the optimal stock amount (4.32) of Theorem 4.5.4 with thresholds $q_\pm(V_{n+1})$. For every $n<N$ and every state $x=(x_0,x_1)\in E$, $x\ne(0,0)$,
--   $$\frac{f^*_n(x)}{h\big(x,f^*_n(x)\big)}=\begin{cases}q_+(V_{n+1}), & \frac{x_1}{x_0}>q_+(V_{n+1}),\\[2pt] \frac{x_1}{x_0}, & q_-(V_{n+1})\le\frac{x_1}{x_0}\le q_+(V_{n+1}),\\[2pt] q_-(V_{n+1}), & \frac{x_1}{x_0}<q_-(V_{n+1}).\end{cases}\tag{4.33}$$
--
--   So the optimal policy moves the stock-to-bond ratio to $q_+(V_{n+1})$ from above, to $q_-(V_{n+1})$ from below, and leaves it unchanged in between.
--
--   **Formalization Note** Ratios are taken in $[0,\infty]$ with $y/0=\infty$ for $y>0$. The cases are tested in the printed order.
--
--   Differences from the source:
--   - encoding: ratios x₁/x₀ and f*/h(x,f*) (possibly with zero denominator) → ratios in [0, ∞] (ℝ≥0∞) with y/0 = ∞ for y > 0; the state (0,0), where x₁/x₀ is undefined, is excluded; reason: the book's quotients are read in [0, ∞]; (4.33) asserts nothing at (0,0)
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), eq. (4.33), p.113 (PDF 127)

import Mathlib
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_Assumptions
import Definitions.Def_BauerleRiederMDP_TransactionCosts_stateSpace
import Definitions.Def_BauerleRiederMDP_TransactionCosts_bondAfter
import Definitions.Def_BauerleRiederMDP_TransactionCosts_ratio
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_V
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_qPlus
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_qMinus
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_optimalStock

open scoped ENNReal

namespace BauerleRiederMDP.TransactionCosts

/-- Property (4.33) of the optimal policy of Theorem 4.5.4 (Bäuerle & Rieder 2011, p.113,
PDF 127): the stock to bond ratio after transaction is
`f*_n(x)/h(x, f*_n(x)) = q₊(V_{n+1})` if `x₁/x₀ > q₊(V_{n+1})`,
`= x₁/x₀` if `q₋(V_{n+1}) ≤ x₁/x₀ ≤ q₊(V_{n+1})`, and `= q₋(V_{n+1})` if `x₁/x₀ < q₋(V_{n+1})`,
for every state `x = (x₀, x₁) ∈ E`, `x ≠ (0, 0)`, and every `n < N`.

**Formalization Note.** Ratios are computed in `[0, ∞]` (`ℝ≥0∞`, with `y/0 = ∞` for `y > 0`).
The state `(0, 0)`, where `x₁/x₀` is undefined, is excluded. The cases are tested in the printed
order; Theorem 4.5.4 shows `q₋(V_{n+1}) ≤ q₊(V_{n+1})`, so they are disjoint. -/
theorem eq_4_33 {Ω : Type*} [MeasurableSpace Ω] (M : Market Ω) (hM : M.Assumptions) :
    ∀ n < M.N, ∀ x ∈ stateSpace, x ≠ 0 →
      ENNReal.ofReal (M.optimalStock n x) /
          ENNReal.ofReal (bondAfter M.c x (M.optimalStock n x)) =
        (if M.qPlus n (M.V (n + 1)) < ratio x then M.qPlus n (M.V (n + 1))
         else if M.qMinus n (M.V (n + 1)) ≤ ratio x then ratio x
         else M.qMinus n (M.V (n + 1))) := by sorry

end BauerleRiederMDP.TransactionCosts
