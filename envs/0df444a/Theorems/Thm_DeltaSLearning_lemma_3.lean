-- Prove2me | Theorems.Thm_DeltaSLearning_lemma_3
-- name    : DeltaSLearning.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:08:26.984586+00:00
-- url     : https://prove2.me/theorems/68edeca4-d1fe-4dae-ba9d-b71efe153eb1
-- title:
--   Lemma 3 — $L$, $G$, $\tilde\nabla$ are $(\nu,b)$-sub-exponential and $\mathbb E[\tilde\nabla^2]\le\nu^2/2$ (corrected: requires $h\le p$, $p<\gamma$ and $\gamma\ge1$)
-- statement:
--   Assume Assumption 1 and the cost parameters of §2, and moreover $h\le p$, $p<\gamma$ and $\gamma\ge1$. Let
--   $$\nu=4\gamma\sqrt{\exp\Bigl(\frac{12\beta\rho p+2p}{h}\Bigr)},\qquad b=2\gamma .$$
--   For every feasible $(\delta,S)$ policy, $0\le\delta\le S\le\beta$:
--
--   1. the cycle length $L(\delta)$, the cycle pseudo cost $G(\delta,S)$ and the stochastic gradient $\tilde\nabla$ of (11) are sub-exponential with parameters $(\nu,b)$;
--   2. $\tilde\nabla^2$ is integrable and $\mathbb E[\tilde\nabla^2]\le\nu^2/2$.
--
--   These are the concentration inputs of Theorem 5, Lemma 4 and Proposition 3.
--
--   The printed lemma has no hypotheses beyond the standing ones and is false without the added three; its proof uses "$p\ge h$ and $\gamma>p$" (p.39) and, when it bounds the tail $e^{-t}$ of $L$ by $e^{-t/\gamma}$, $\gamma\ge1$.
--
--   Differences from the source:
--   - correction: no hypotheses beyond Assumption 1 and the cost parameters → adds h ≤ p, p < γ and γ ≥ 1; reason: the printed lemma is false. (i) β = 1, D ~ U[0, 0.01] (ρ = 100), h = 1000, p = 0.01, c = 0, K = 0.01, δ = S = 1: L ≥ 100 and x_{L+1} = 0, so ∇̃ ≥ 98 999.99 and E[∇̃²] ≥ 9.8·10⁹ > ν²/2 ≈ 8.1·10⁶, so (b) fails. (ii) β = 0.01, D ~ U[0, 1] (ρ = 1), h = p = 1, c = 0, K = 0.01 (γ = 0.03 < p), δ = S = β: ∇̃ = −1 with probability 0.99, so E[∇̃²] ≥ 0.99 > ν²/2 ≈ 0.060, so (b) fails. (iii) β = 0.01, D ~ U[0, 1] (ρ = 1), h = p = 0.01, c = 0, K = 0.02 (h ≤ p < γ = 0.0202 < 1), δ = S = β: P(L = 2) ≈ 0.01, E[L] ≈ 1.0101, and at λ = 24 < 1/b ≈ 24.75 the moment E[e^{λ(L−E L)}] ≥ 0.0099·e^{23.76} ≈ 2·10⁸ exceeds e^{ν²λ²/2} ≈ 6.4·10⁶, so (a) fails for L. The proof uses p ≥ h and γ > p (p.39) and γ ≥ 1 where it bounds 2e^{6βρ+1}e^{−t} by a multiple of e^{−t/γ}
--   - encoding: sub-exponential with parameters (ν, b) (Definition 5) → the published HighDimStat.TailBounds.IsSubExponential with parameters (ν, b); reason: it is Definition 5, plus the integrability its expectations presuppose
--   - reading: c and h are per-unit ordering and holding costs, sign not stated (p.7) → c ≥ 0 and h > 0; reason: costs are nonnegative; (19) divides by h, and for c < 0 the bound γ of (10) can be negative, so Lemma 1 would fail
--   - reading: i.i.d. continuous demands whose pdf satisfies f(d) ≤ ρ for d ≥ 0 (Assumption 1) → D t measurable, iIndepFun, IdentDistrib to D 0, and the law of D 0 is ≤ ρ·Lebesgue on [0, ∞); reason: demands are nonnegative quantities (Lemma 2 and the proof of Lemma 3: "D is positive"); the measure inequality is exactly a Lebesgue density bounded by ρ and supported on [0, ∞)
--   - encoding: periods t = 1, 2, … → 0-based: D t is the demand of period t + 1; reason: Lean indexing; no instance changes
--   - encoding: E[∇̃²] (finiteness presupposed) → integrability of ∇̃² stated as an extra conclusion; reason: Bochner integrals are 0 on non-integrable functions; the conclusion rules out that junk reading and holds because the expectation is finite
-- source:
--   Yuan, Luo, Shi, Marrying SGD with Bandits, SSRN 3329611 (accepted manuscript, Management Science 2021, doi:10.1287/mnsc.2020.3799), Lemma 3, eq. (31), p.23; proof pp.38–39

import Mathlib
import Definitions.Def_HighDimStat_TailBounds_IsSubExponential
import Definitions.Def_DeltaSLearning_IsDemandProcess
import Definitions.Def_DeltaSLearning_cycleCost
import Definitions.Def_DeltaSLearning_cycleGrad
import Definitions.Def_DeltaSLearning_nu
import Definitions.Def_DeltaSLearning_bSub

open MeasureTheory ProbabilityTheory

namespace DeltaSLearning

/-- **Lemma 3** (sub-exponentials), corrected. Assume moreover `h ≤ p`, `p < γ` and `γ ≥ 1`.
For every feasible `(δ, S)` policy (`0 ≤ δ ≤ S ≤ β`):
(a) the cycle length `L`, the cycle pseudo cost `G` and the stochastic gradient `∇̃` of (11)
are sub-exponential with parameters `(ν, b)`, `ν = 4γ√(exp((12βρp + 2p)/h))`, `b = 2γ`;
(b) `E[∇̃²] ≤ ν²/2`.
Yuan, Luo, Shi, SSRN 3329611 (Management Science 2021, doi:10.1287/mnsc.2020.3799), Lemma 3 and eq. (31), p.23; proof pp.38–39.

**Formalization Note** The printed lemma has no hypotheses beyond the standing ones and is false
without the three added ones; its proof uses "p ≥ h and γ > p" (p.39) and, when it bounds the tail
`e^{-t}` of `L` by `e^{-t/γ}`, `γ ≥ 1`. Counterexamples are in the item's description.
Sub-exponential is the published `HighDimStat.TailBounds.IsSubExponential` (Definition 5, p.43).
Integrability of `∇̃²` is stated as a conclusion. -/
theorem lemma_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : ℕ → Ω → ℝ) (cp : Params) (hD : IsDemandProcess P D cp.ρ) (hhp : cp.h ≤ cp.p)
    (hpγ : cp.p < gamma cp) (hγ : 1 ≤ gamma cp) :
    ∀ δ S : ℝ, 0 ≤ δ → δ ≤ S → S ≤ cp.β →
      HighDimStat.TailBounds.IsSubExponential (fun ω => (cycleLength δ (fun t => D t ω) : ℝ)) P
          (nu cp) (bSub cp) ∧
        HighDimStat.TailBounds.IsSubExponential (fun ω => cycleCost cp δ S (fun t => D t ω)) P
          (nu cp) (bSub cp) ∧
        HighDimStat.TailBounds.IsSubExponential (fun ω => cycleGrad cp δ S (fun t => D t ω)) P
          (nu cp) (bSub cp) ∧
        Integrable (fun ω => cycleGrad cp δ S (fun t => D t ω) ^ 2) P ∧
        ∫ ω, cycleGrad cp δ S (fun t => D t ω) ^ 2 ∂P ≤ nu cp ^ 2 / 2 := by sorry

end DeltaSLearning
