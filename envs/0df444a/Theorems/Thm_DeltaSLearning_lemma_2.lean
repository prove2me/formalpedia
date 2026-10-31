-- Prove2me | Theorems.Thm_DeltaSLearning_lemma_2
-- name    : DeltaSLearning.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:06:33.992998+00:00
-- url     : https://prove2.me/theorems/49eedf38-a8ed-4020-a82f-410f87f9f9f3
-- title:
--   Lemma 2 — $\mathbb E[L(\delta)]$ is $6\rho$-Lipschitz
-- statement:
--   Let $D_1,D_2,\dots$ be i.i.d. positive random variables whose density is bounded by $\rho$, and let $W_0=0$, $W_t=D_1+\dots+D_t$. For $\delta>0$ let $L(\delta)=\min\{t: W_t\ge\delta\}$ be the hitting time of $[\delta,\infty)$. Then $\mathbb E[L(\delta)]<\infty$ for every $\delta>0$ and
--   $$\bigl|\mathbb E[L(\delta_1)]-\mathbb E[L(\delta_2)]\bigr|\le 6\rho\,|\delta_1-\delta_2|\qquad(\delta_1,\delta_2>0).$$
--
--   The expected cycle length of a $(\delta,S)$ policy is therefore Lipschitz in the gap, which drives the Lipschitz continuity of $V^*(\delta)$ (Theorem 2(c)).
--
--   Differences from the source:
--   - encoding: i.i.d. positive random variables with densities bounded by ρ → D satisfies Assumption 1: measurable, iIndepFun, IdentDistrib, law of D 0 ≤ ρ·Lebesgue on [0, ∞); reason: a density ≤ ρ on [0, ∞) has no atom at 0, so the D_t are positive a.s.; the same set of laws
--   - encoding: L(δ) = min{t : W_t ≥ δ} → L(δ) = min{t ≥ 1 : W_t ≥ δ}; reason: equal for δ > 0, the lemma's range
--   - encoding: periods t = 1, 2, … → 0-based: D t is the demand of period t + 1; reason: Lean indexing; no instance changes
--   - encoding: E[L(δ)] (finiteness presupposed) → integrability of L(δ) stated as an extra conclusion; reason: Bochner integrals are 0 on non-integrable functions; the conclusion rules out that junk reading and holds because the expectation is finite
-- source:
--   Yuan, Luo, Shi, Marrying SGD with Bandits, SSRN 3329611 (accepted manuscript, Management Science 2021, doi:10.1287/mnsc.2020.3799), Lemma 2, p.12

import Mathlib
import Definitions.Def_DeltaSLearning_IsDemandProcess
import Definitions.Def_DeltaSLearning_cycleLength

open MeasureTheory ProbabilityTheory

namespace DeltaSLearning

/-- **Lemma 2** (Lipschitz hitting time of ascending random walk). For i.i.d. demands with a
density bounded by `ρ`, the expected hitting time `E[L(δ)]` of `[δ, ∞)` by the walk
`W_t = D_1 + ⋯ + D_t` is finite for every `δ > 0` and `6ρ`-Lipschitz in `δ > 0`.
Yuan, Luo, Shi, SSRN 3329611 (Management Science 2021, doi:10.1287/mnsc.2020.3799), Lemma 2, p.12.

**Formalization Note** `L(δ)` is `cycleLength δ`, the first `t ≥ 1` with `W_t ≥ δ`, which is
the page's `min{t : W_t ≥ δ}` for `δ > 0`. "Positive" demands follow from Assumption 1's density
(no atom at 0). Finiteness of `E[L(δ)]`, which the page presupposes, is stated as a conclusion. -/
theorem lemma_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : ℕ → Ω → ℝ) (ρ : ℝ) (hρ : 0 < ρ) (hD : IsDemandProcess P D ρ) :
    (∀ δ : ℝ, 0 < δ → Integrable (fun ω => (cycleLength δ (fun t => D t ω) : ℝ)) P) ∧
      LipschitzOnWith (Real.toNNReal (6 * ρ))
        (fun δ : ℝ => ∫ ω, (cycleLength δ (fun t => D t ω) : ℝ) ∂P) (Set.Ioi 0) := by sorry

end DeltaSLearning
