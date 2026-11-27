-- Prove2me | Theorems.Thm_BauerleRiederMDP_LQ_Supplement_theorem_9_4_2
-- name    : BauerleRiederMDP.LQ.Supplement.theorem_9_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T00:07:51.55605+00:00
-- url     : https://prove2.me/theorems/597b162a-de75-5481-8cd3-c8d4953fb659
-- title:
--   Theorem 9.4.2 — trade execution: unique fixed point in IM_cx and an optimal feedback rule with unit increments
-- statement:
--   a) The value function $V(t, x)$ is the unique fixed point of $T$ in $IM_cx$. b) There exists an optimal Markov strategy $\pi ^* = (\pi ^*_t)$ with $\pi ^*_t = f^*(t, X_{t-})$, where $f^*$ satisfies $f^*(t, x) \le  f^*(t, x + 1) \le  f^*(t, x) + 1$, and $(X_t)$ is the corresponding number of shares process.
--
--   **Formalization Note.** $V$ is the infimum of the expected cost over all admissible predictable control processes (`TradeExec.V`), finite ($V \le  C(x)$) and read as a real function $Vr$; $T$ and $IM_cx$ are those of p.295, all statements on $E = [0, T] \times  \mathbb N _0$. $f^*$ is the smallest minimizer (9.22) for $v = V$. The strategy $\pi ^*$ sells, between the jumps $T_n$ and $T_{n+1}$, the amount $f^*(t, Z_n)$ at time $t = T_n + s$, i.e. $\pi ^*_t = f^*(t, X_{t-})$; it is admissible ($f^*(t, x) \le  x$) and measurable, and optimal: its cost is $V$ at every $(t, x) \in  E$.
--
--   Differences from the source:
--   - encoding: π_t ≤ X_t for t ∈ [0,T] → rules satisfy g_n ≤ Z_n at every argument; reason: values off reachable arguments are never used; same costs
--   - reading: f* of (9.22) → the smallest minimizer for v = V; reason: the book's choice
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 9.4.2, p.296 (PDF 306)

import Mathlib
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_TradeExec
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_TradeStrategy
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_TradeExec_state
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_TradeExec_Vstrat
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_TradeExec_V
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_TradeExec_Top
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_TradeExec_IMcx
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_TradeExec_fstar

namespace BauerleRiederMDP.LQ.Supplement

/-- **Theorem 9.4.2** (trade execution) (Bäuerle & Rieder, *Markov Decision Processes with
Applications to Finance* (2011), Theorem 9.4.2, p.296, PDF 306, problem of §9.4, pp.293–295,
PDF 303–305).
a) The value function `V(t, x)` is the unique fixed point of `T` in `IM_cx`.
b) There exists an optimal Markov strategy `π* = (π*_t)` with `π*_t = f*(t, X_{t−})`, where `f*`
satisfies `f*(t, x) ≤ f*(t, x + 1) ≤ f*(t, x) + 1`, and `(X_t)` is the corresponding number of
shares process.

**Formalization Note.** `V` is the infimum of the expected cost over all admissible predictable
control processes (`TradeExec.V`), finite (`V ≤ C(x)`) and read as a real function `Vr`; `T` and
`IM_cx` are those of p.295, all statements on `E = [0, T] × ℕ_0`. `f*` is the smallest minimizer
(9.22) for `v = V`. The strategy `π*` sells, between the jumps `T_n` and `T_{n+1}`, the amount
`f*(t, Z_n)` at time `t = T_n + s`, i.e. `π*_t = f*(t, X_{t−})`; it is admissible (`f*(t, x) ≤ x`)
and measurable, and optimal: its cost is `V` at every `(t, x) ∈ E`. -/
theorem theorem_9_4_2 (P : TradeExec) :
    let Vr : ℝ × ℕ → ℝ := fun p => (P.V p).toReal
    let f : ℝ × ℕ → ℕ := P.fstar Vr
    -- a)
    ((∀ p, P.V p ≠ ⊤) ∧ Vr ∈ P.IMcx ∧ (∀ t ∈ Set.Icc 0 P.T, ∀ x, P.Top Vr (t, x) = Vr (t, x)) ∧
      ∀ w ∈ P.IMcx, (∀ t ∈ Set.Icc 0 P.T, ∀ x, P.Top w (t, x) = w (t, x)) →
        ∀ t ∈ Set.Icc 0 P.T, ∀ x, w (t, x) = Vr (t, x)) ∧
    -- b)
    ((∃ g : TradeStrategy, (∀ n q, (g n).1 q = f (q.2.2.1 + q.1, q.2.2.2)) ∧
        ∀ t ∈ Set.Icc 0 P.T, ∀ x, P.Vstrat g (t, x) = P.V (t, x)) ∧
      ∀ t ∈ Set.Icc 0 P.T, ∀ x, f (t, x) ≤ f (t, x + 1) ∧ f (t, x + 1) ≤ f (t, x) + 1) := by sorry

end BauerleRiederMDP.LQ.Supplement
