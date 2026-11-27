-- Prove2me | Theorems.Thm_ComplementarySourcing_Supplement_theorem_a1
-- name    : ComplementarySourcing.Supplement.theorem_a1
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T03:50:09.840779+00:00
-- url     : https://prove2.me/theorems/61e688f1-af9d-5d6f-b448-1dcd1266b3d5
-- title:
--   Theorem A1 — under general discrete market risk, $r\mu\ge2\epsilon_1+\max\{(\epsilon_0-p_1\epsilon_1)/p_1,\epsilon_1^2/(2\epsilon_n)\}$ gives $\pi_m^{M*}>\pi_m^{S*}$
-- statement:
--   Let the market taste be $\epsilon=\epsilon_i$ with probability $p_i>0$, $i=1,\dots,n$, $\sum_ip_i=1$, ordered $\epsilon_1\ge\epsilon_2\ge\dots\ge\epsilon_n>0$, with mean $\epsilon_0=\sum_ip_i\epsilon_i$. In Model (M) the manufacturer chooses its effort and the wholesale price first; in Model (S) the supplier does; the second mover observes the realized $\epsilon$. Let $\mu>0$, $\alpha\ge0$, and suppose
--
--   $$r\mu\ \ge\ 2\epsilon_1+\max\Big\{\frac{\epsilon_0-p_1\epsilon_1}{p_1},\ \frac{\epsilon_1^2}{2\epsilon_n}\Big\}.$$
--
--   Then, for every equilibrium of each model, the manufacturer earns strictly more as the first mover: $\pi_m^{M*}>\pi_m^{S*}$.
--
--   The paper proves Theorem 2 from the proof of this theorem at $n=2$, $\epsilon_{1,2}=\epsilon_0\pm\sigma$, $p_1=p_2=\tfrac12$ (p.A11).
--
--   **Formalization Note** The support is indexed by $\{0,\dots,n\}$ ($n+1\ge1$ points): the page's $\epsilon_1$ is index $0$ and its $\epsilon_n$ the last index.
--
--   Differences from the source:
--   - reading: µ is "a scaling parameter for market size" (p.7) → 0 < μ; reason: a market-size scale is positive; at µ = 0 every demand is 0
--   - encoding: the optimal profits π^{M∗}, π^{S∗} of the two models → the leader's and follower's payoffs at every equilibrium of each model; reason: the page's optimum is determined by backward induction; quantifying over all equilibria changes no instance where it is unique
--   - encoding: the second mover's best response x*(·) → an arbitrary follower strategy s with IsFollowerStrategy; reason: the best response as a map from the leader's move (and the state) to an effort; its values are best responses at every feasible move
--   - reading: the quotient ϵ1²/(2ϵn) of a market-taste support → 0 < ε (Fin.last n); reason: the quotient is undefined at ϵn = 0 and market taste is not negative; excludes only supports reaching 0 or below
--   - reading: ϵ = ϵi with probability pi → 0 < p i for every i, Σ p i = 1; reason: a probability law whose listed points are its support; the page divides by p1
--   - encoding: i ∈ {1, …, n}, ϵ1 ≥ ⋯ ≥ ϵn, ϵ0 = Σ pi ϵi → ε, p : Fin (n + 1) → ℝ, Antitone ε, ε₀ = Σ p i * ε i; reason: 0-based indexing of n + 1 points; n + 1 ranges over every support size ≥ 1
-- source:
--   Wang, Yin, Chen, Webster, Investment Efforts Under Complementary Sourcing, SSRN 3592730 (PDF of March 1, 2022), §A1, p.A1; Theorem A1, p.A5; proof p.A6

import Mathlib
import Definitions.Def_ComplementarySourcing_StackelbergGame_IsEquilibrium
import Definitions.Def_ComplementarySourcing_Supplement_DiscreteM_game
import Definitions.Def_ComplementarySourcing_Supplement_DiscreteS_game
import Definitions.Def_ComplementarySourcing_Supplement_expectedManufacturerProfit

namespace ComplementarySourcing.Supplement

/-- **Theorem A1** (general discrete market risk). Let `ϵ = ϵ_i` with probability `p_i`,
`i = 1, …, n`, with `ϵ₁ ≥ ϵ₂ ≥ ⋯ ≥ ϵ_n`, and `ϵ₀ = Σ_i p_i ϵ_i`. Suppose
`rµ ≥ 2ϵ₁ + max{(ϵ₀ − p₁ϵ₁)/p₁, ϵ₁²/(2ϵ_n)}`. Then `π^{M∗}_m > π^{S∗}_m`.
Wang, Yin, Chen, Webster, *Investment Efforts Under Complementary Sourcing*, SSRN 3592730
(PDF of March 1, 2022), §A1, p.A1 (PDF 29), and Theorem A1, p.A5 (PDF 33); proof p.A6 (PDF 34).

**Formalization Note.** The support has `n + 1 ≥ 1` points indexed by `Fin (n + 1)`: the page's
`ϵ₁` is `ε 0` and its `ϵ_n` is `ε (Fin.last n)`. The ordering is `Antitone ε`; `p_i > 0`, `Σ p_i = 1`.
`0 < ϵ_n` is the positive-support reading of the quotient `ϵ₁²/(2ϵ_n)`. The conclusion holds for
every equilibrium `(sM, xM, wM)` of Model (M) and `(sS, xS, wS)` of Model (S), for every `α ≥ 0`;
`π^{S∗}_m` is the manufacturer's expected profit as second mover. -/
theorem theorem_a1 {n : ℕ} {μ α r ε₀ xM wM xS wS : ℝ} {ε p : Fin (n + 1) → ℝ}
    {sM sS : ℝ × ℝ → Fin (n + 1) → ℝ}
    (hμ : 0 < μ) (hα : 0 ≤ α) (hε : Antitone ε) (hεn : 0 < ε (Fin.last n))
    (hp : ∀ i, 0 < p i) (hp₁ : ∑ i, p i = 1) (hε₀ : ε₀ = ∑ i, p i * ε i)
    (hr : r * μ ≥ 2 * ε 0 + max ((ε₀ - p 0 * ε 0) / p 0) (ε 0 ^ 2 / (2 * ε (Fin.last n))))
    (hM : (Supplement.DiscreteM.game μ α r ε p).IsEquilibrium sM (xM, wM))
    (hS : (Supplement.DiscreteS.game μ α r ε p).IsEquilibrium sS (xS, wS)) :
    (Supplement.DiscreteM.game μ α r ε p).leaderPayoff (xM, wM) (sM (xM, wM)) >
      Supplement.expectedManufacturerProfit μ α r xS wS ε p (sS (xS, wS)) := by sorry

end ComplementarySourcing.Supplement
