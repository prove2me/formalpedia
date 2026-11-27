-- Prove2me | Theorems.Thm_BauerleRiederMDP_LQ_Supplement_theorem_4_2_2
-- name    : BauerleRiederMDP.LQ.Supplement.theorem_4_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T23:51:17.155482+00:00
-- url     : https://prove2.me/theorems/b3ce53c7-1ce4-52fe-ae91-30e00042371c
-- title:
--   Theorem 4.2.2 (corrected: existence of maximizers) — terminal wealth problem: structure, Bellman equation, optimal strategy
-- statement:
--   For the multiperiod terminal wealth problem it holds: a) the value functions $V_n$ are strictly increasing, strictly concave and continuous; b) they can be computed recursively by the Bellman equation $V_N(x) = U(x)$, $V_n(x) = \sup _{a \in  D_n(x)} \mathbb E  V_{n+1}((1 + i_{n+1})(x + a \cdot  R_{n+1}))$, $x \in  E$; c) there exist maximizers $f^*_n$ of $V_{n+1}$ (**if $dom U = [0, \infty )$, or every $D_n(x)$ is closed, or $U'(0+) = \infty $**), and the portfolio strategy $(f^*_0, \dots , f^*_{N-1})$ is optimal for the $N$-stage terminal wealth problem.
--
--   **Formalization Note.** Standing assumptions of §4.2: $U$ is a utility function (Definition 3.4.1) with $dom U = [0, \infty )$ or $(0, \infty )$, the returns are independent and Assumption (FM) holds; the state space is $E = dom U$ at every stage. The existence clause of c) is false as printed for some utilities on $(0, \infty )$: $d = N = 1$, $i = 0$, $\mathbb P (R = -1/2) = 1/10$, $\mathbb P (R = 1) = 9/10$, $U(w) = \log (1 + w)$ give $D_0(1) = (-1, 2)$ and $a \mapsto  \mathbb E  U(1 + aR)$ strictly increasing there, so no maximizer exists at $x = 1$. The repair is that of the published Theorem 6.1.1 d) ($U'(0+) = \infty $ in difference-quotient form, which covers $U(0+) = -\infty $). Optimality of every sequence of maximizers needs no premise. a) is stated for a real function equal to $V_n$ on $dom U$; optimality means $V_{0\pi }(x) = V_0(x)$ for $x \in  E$ (p.18).
--
--   Differences from the source:
--   - correction: there exist maximizers f*_n of V_{n+1} → maximizers exist if dom U = [0,∞), or every D_n(x) is closed, or U′(0+) = ∞; reason: false as printed: d = N = 1, i = 0, ℙ(R = −1/2) = 1/10, ℙ(R = 1) = 9/10, U(w) = log(1+w) on (0,∞): D_0(1) = (−1,2) and a ↦ 𝔼U(1 + aR) is strictly increasing there, so no maximizer exists at x = 1
--   - encoding: V_n strictly concave on dom U → a real function equal to V_n on dom U is strictly concave; reason: EReal-valued V_n; same statement
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 4.2.2, p.81 (PDF 95)

import Mathlib
import Definitions.Def_BauerleRiederMDP_RegimeSwitching_eint
import Definitions.Def_BauerleRiederMDP_NoArbitrage_IsUtilityFunction
import Definitions.Def_BauerleRiederMDP_PartialObs_S0
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_TWMarket
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_TWMarket_FM
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_TWMarket_wealth
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_TWMarket_D
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_TWMarket_IsPolicy
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_TWMarket_Vpi
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_TWMarket_V
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_TWMarket_bellmanQ
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_TWMarket_IsMaximizer

open MeasureTheory
open BauerleRiederMDP.NoArbitrage (IsUtilityFunction)

namespace BauerleRiederMDP.LQ.Supplement

/-- **Theorem 4.2.2** (corrected existence clause of part c) (Bäuerle & Rieder, *Markov Decision
Processes with Applications to Finance* (2011), Theorem 4.2.2, p.81, PDF 95, with the model of
§4.2, pp.79–80, PDF 93–94). For the multiperiod terminal wealth problem it holds:
a) the value functions `V_n` are strictly increasing, strictly concave and continuous;
b) they can be computed recursively by the Bellman equation `V_N(x) = U(x)`,
`V_n(x) = sup_{a ∈ D_n(x)} 𝔼 V_{n+1}((1 + i_{n+1})(x + a · R_{n+1}))`, `x ∈ E`;
c) there exist maximizers `f*_n` of `V_{n+1}` (**if `dom U = [0, ∞)`, or every `D_n(x)` is closed, or
`U′(0+) = ∞`**), and the portfolio strategy `(f*_0, …, f*_{N−1})` is optimal for the `N`-stage
terminal wealth problem.

**Formalization Note.** Standing assumptions of §4.2: `U` is a utility function (Definition 3.4.1)
with `dom U = [0, ∞)` or `(0, ∞)`, the returns are independent and Assumption (FM) holds; the state
space is `E = dom U` at every stage. The existence clause of c) is false as printed for some
utilities on `(0, ∞)`: `d = N = 1`, `i = 0`, `ℙ(R = −1/2) = 1/10`, `ℙ(R = 1) = 9/10`,
`U(w) = log(1 + w)` give `D_0(1) = (−1, 2)` and `a ↦ 𝔼 U(1 + aR)` strictly increasing there, so no
maximizer exists at `x = 1`. The repair is that of the published Theorem 6.1.1 d)
(`U′(0+) = ∞` in difference-quotient form, which covers `U(0+) = −∞`). Optimality of every
sequence of maximizers needs no premise. a) is stated for a real function equal to `V_n` on
`dom U`; optimality means `V_{0π}(x) = V_0(x)` for `x ∈ E` (p.18). -/
theorem theorem_4_2_2 {d N : ℕ} (Mk : TWMarket d) (hFM : Mk.FM N) (dom : Set ℝ)
    (hdom : dom = Set.Ici 0 ∨ dom = Set.Ioi 0) (U : ℝ → ℝ) (hU : IsUtilityFunction dom U) :
    (∀ n ≤ N, ∃ v : ℝ → ℝ, (∀ x ∈ dom, Mk.V (fun _ => dom) U N n x = (v x : EReal)) ∧
      IsUtilityFunction dom v) ∧
    (∀ x ∈ dom, Mk.V (fun _ => dom) U N N x = (U x : EReal)) ∧
    (∀ n < N, ∀ x ∈ dom, Mk.V (fun _ => dom) U N n x =
      ⨆ a ∈ Mk.D (fun _ => dom) n x, Mk.bellmanQ n (Mk.V (fun _ => dom) U N (n + 1)) x a) ∧
    (((dom = Set.Ici 0 ∨ (∀ n < N, ∀ x ∈ dom, IsClosed (Mk.D (fun _ => dom) n x)) ∨
        ∀ K : ℝ, ∃ δ : ℝ, 0 < δ ∧ ∀ s t : ℝ, 0 < s → s < t → t < δ → K * (t - s) ≤ U t - U s) →
      ∀ n < N, ∃ f : ℝ → Fin d → ℝ,
        Mk.IsMaximizer (fun _ => dom) n (Mk.V (fun _ => dom) U N (n + 1)) f)) ∧
    (∀ fstar : ℕ → ℝ → Fin d → ℝ,
      (∀ n < N, Mk.IsMaximizer (fun _ => dom) n (Mk.V (fun _ => dom) U N (n + 1)) (fstar n)) →
      Mk.IsPolicy (fun _ => dom) N fstar ∧
        ∀ x ∈ dom, Mk.Vpi U N fstar 0 x = Mk.V (fun _ => dom) U N 0 x) := by sorry

end BauerleRiederMDP.LQ.Supplement
