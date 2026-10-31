-- Prove2me | Theorems.Thm_DeltaSLearning_lemma_4
-- name    : DeltaSLearning.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:10:55.977049+00:00
-- url     : https://prove2.me/theorems/f966601d-7d23-4942-afa6-452b79c686c2
-- title:
--   Lemma 4 — estimation confidence bound $|\hat V^n_j-V^*_j|\le\theta\log(8/\kappa)/\sqrt n$ (corrected: requires $h\le p$, $p<\gamma$ and $\gamma\ge1$)
-- statement:
--   Assume Assumption 1, the cost parameters of §2 and, as in the corrected Lemma 3, $h\le p$, $p<\gamma$ and $\gamma\ge1$. Run the $(\delta,S)$ learning algorithm with Theorem 3's step sizes $\eta^n=\beta/(\xi\sqrt n)$, any $J\ge1$, any confidence sizes and any initial targets $S^1_j\in[\delta_j,\beta]$. For every $j\in[J]$, every epoch $n\ge1$ and every $\kappa\in(0,1)$, with probability at least $1-\kappa$: if $j$ is active in epoch $n$, then
--   $$\bigl|\hat V^n_j-V^*_j\bigr|\le\frac{\theta\log(8/\kappa)}{\sqrt n},\qquad \hat V^n_j=\frac{\hat G^n_j}{\hat L^n_j},\quad \theta=(2\gamma+4)\max(\nu,b)+1.5\beta\xi .$$
--
--   With $\kappa=1/N^2$ this is the event on which the pruning step never removes the best grid gap (Proposition 2).
--
--   Differences from the source:
--   - correction: no hypotheses beyond Assumption 1 and the cost parameters → adds h ≤ p, p < γ and γ ≥ 1; reason: the printed lemma is false. β = 10⁻⁵, D ~ U[0, 2β] (ρ = 1/(2β)), h = 1, p = 0.1, c = 0, K = 10⁻⁸, J = 10, j = 1 (δ₁ = 0.1β), S¹₁ = β, n = 10⁶, κ = 1/2. Then γ ≈ 1.101·10⁻⁵, ξ ≈ 4.65β and θ ≈ 26.3β, so θ log(8/κ)/√n ≈ 0.073β. For all n ≤ 10⁶, ηⁿ|∇̃| ≥ 0.2153·0.1/√n ≥ 2.1·10⁻⁵ > β, so every SGD step lands on an endpoint of [δ₁, β] and Sⁿ₁ is a two-state chain that spends about 65% of the epochs at β, where V is far above its minimum. Simulation (two runs of 10⁶ epochs) gives V̂ⁿ₁ ≈ 0.1125β while V*₁ ≈ −0.0078β, an error of 0.12β. The same instance with J = 1000, j = 100 and Theorem 3's Δⁿ (N = 10⁶) fails too: Δⁿ ≥ 1.5β exceeds every gap, so nothing is pruned. The proof takes ξ and the sub-exponential parameters of ∇̃ from Lemma 3, so it needs Lemma 3's hypotheses; Proposition 2 and the goal are not corrected, because they carry a free constant and the width Δⁿ has a factor log N
--   - reading: with probability at least 1 − κ, |V̂ⁿ_j − V*_j| ≤ θ log(8/κ)/√n → P(j ∈ 𝒜ⁿ and |V̂ⁿ_j − V*_j| > θ log(8/κ)/√n) ≤ κ; reason: V̂ⁿ_j is updated only while j is active; Proposition 2 uses the lemma for active indices (pp.24–25)
--   - generalization: inside the proof of Theorem 3, with its parameters → Theorem 3's step sizes, any J ≥ 1, any confidence sizes and any initialization; reason: the proof uses only the step sizes (through Theorem 5); this specializes to Theorem 3's J and Δ
--   - reading: epoch n implements (δⁿ, Sⁿ) = (δ_{jⁿ}, max(xⁿ, Sⁿ_{jⁿ})) (14), runs while the epoch's sales ≤ δ̄ⁿ and completes the current cycle (Algorithm 1) → first period orders up to Sⁿ, later periods use the (δⁿ, Sⁿ) rule; the while-loop ends at the first period whose cumulative sales exceed δ̄ⁿ; the epoch ends at the first later period ending with inventory ≤ Sⁿ − δⁿ; reason: the proof's "forced to take xⁿ⁺¹ instead" (p.26) and the term c(Sⁿ⁺¹ − Sⁿ) (p.19); "keep running (δⁿ,Sⁿ) policy until inventory drops below Sⁿ − δⁿ" (Algorithm 1)
--   - reading: jⁿ := argmax_{j ∈ 𝒜ⁿ} Sⁿ_j (13), no tie-break → smallest maximizing index; reason: the proof uses only jⁿ ∈ 𝒜ⁿ and Sⁿ_{jⁿ} = max_{j ∈ 𝒜ⁿ} Sⁿ_j
--   - reading: c and h are per-unit ordering and holding costs, sign not stated (p.7) → c ≥ 0 and h > 0; reason: costs are nonnegative; (19) divides by h, and for c < 0 the bound γ of (10) can be negative, so Lemma 1 would fail
--   - reading: i.i.d. continuous demands whose pdf satisfies f(d) ≤ ρ for d ≥ 0 (Assumption 1) → D t measurable, iIndepFun, IdentDistrib to D 0, and the law of D 0 is ≤ ρ·Lebesgue on [0, ∞); reason: demands are nonnegative quantities (Lemma 2 and the proof of Lemma 3: "D is positive"); the measure inequality is exactly a Lebesgue density bounded by ρ and supported on [0, ∞)
--   - encoding: periods t = 1, 2, … → 0-based: D t is the demand of period t + 1; reason: Lean indexing; no instance changes
-- source:
--   Yuan, Luo, Shi, Marrying SGD with Bandits, SSRN 3329611 (accepted manuscript, Management Science 2021, doi:10.1287/mnsc.2020.3799), Lemma 4, eq. (32), p.24; eq. (30), p.22; proof pp.41–42

import Mathlib
import Definitions.Def_DeltaSLearning_IsDemandProcess
import Definitions.Def_DeltaSLearning_algState__6eb4c5
import Definitions.Def_DeltaSLearning_optAvgCostGap
import Definitions.Def_DeltaSLearning_stepSize
import Definitions.Def_DeltaSLearning_theta

open MeasureTheory ProbabilityTheory

namespace DeltaSLearning

/-- **Lemma 4** (estimation confidence bound), corrected. Assume moreover `h ≤ p`, `p < γ` and
`γ ≥ 1`, the hypotheses of the corrected Lemma 3. Run the `(δ, S)` learning algorithm with Theorem 3's
step sizes `ηⁿ = β/(ξ√n)`, any `J ≥ 1`, any confidence sizes and any initial targets
`S¹_j ∈ [δ_j, β]`. For every `j ∈ [J]`, epoch `n ≥ 1` and `κ ∈ (0, 1)`, with probability at
least `1 - κ`, if `j` is active in epoch `n` then
`|V̂ⁿ_j - V*_j| ≤ θ log(8/κ)/√n`, where `V̂ⁿ_j = Ĝⁿ_j/L̂ⁿ_j` (30) and
`θ = (2γ + 4) max(ν, b) + 1.5βξ` (32).
Yuan, Luo, Shi, SSRN 3329611 (Management Science 2021, doi:10.1287/mnsc.2020.3799), Lemma 4 and eq. (32), p.24; eq. (30), p.22; proof pp.41–42.

**Formalization Note** The printed lemma has no hypotheses beyond the standing ones and is false
without the three added ones (counterexample in the item's description); its proof obtains the
second-moment bound `ξ²` and the sub-exponential parameters of `∇̃` from Lemma 3, which needs them.
`V̂ⁿ_j` is defined only while `j` is active; the guard `j ∈ 𝒜ⁿ` is how
Proposition 2 uses the lemma (pp.24–25). The event is stated as its complement: the probability
that `j ∈ 𝒜ⁿ` and the bound fails is at most `κ`. `𝒜ⁿ` is the active set of the state at the
beginning of epoch `n` (`algState … (n - 1)`) and `Ĝⁿ_j`, `L̂ⁿ_j` are read from the state after
it (`algState … n`). -/
theorem lemma_4 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : ℕ → Ω → ℝ) (cp : Params) (hD : IsDemandProcess P D cp.ρ) (hhp : cp.h ≤ cp.p)
    (hpγ : cp.p < gamma cp) (hγ : 1 ≤ gamma cp) (J : ℕ) (hJ : 1 ≤ J)
    (Δ : ℕ → ℝ) (S₁ : ℕ → ℝ) (hS₁ : ∀ j ∈ Finset.Icc 1 J, S₁ j ∈ Set.Icc (grid cp.β J j) cp.β)
    (j : ℕ) (hj : j ∈ Finset.Icc 1 J) (n : ℕ) (hn : 1 ≤ n) (κ : ℝ) (hκ₀ : 0 < κ) (hκ₁ : κ < 1) :
    let σ : Ω → ℕ → AlgState := fun ω k => algState cp J (stepSize cp) Δ S₁ (fun t => D t ω) k
    P {ω | j ∈ (σ ω (n - 1)).A ∧
        theta cp * Real.log (8 / κ) / Real.sqrt n <
          |(σ ω n).Ghat j / (σ ω n).Lhat j - optAvgCostGap P D cp (grid cp.β J j)|}
      ≤ ENNReal.ofReal κ := by sorry

end DeltaSLearning
