-- Prove2me | Theorems.Thm_AgnHalfMem_lemma_4_7
-- name    : AgnHalfMem.lemma_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:12:54.164912+00:00
-- url     : https://prove2.me/theorems/8195518c-9a9d-4847-a8ed-d9c2b0fbbabe
-- title:
--   Lemma 4.7 — $2^{\Omega(d)}$ nearly orthogonal functions, each correlated with a halfspace
-- statement:
--   There are universal constants $c_1,c_2,a,b>0$ with the following property. Let $\mu$ be a probability measure on $\mathbb R$ with finite non-zero variance and half-variance radius $L_\mu\le c_2\sqrt d$, and let $\tau\in[c_1,\ \sqrt d/(4L_\mu)]$. Then there are $m\ge 2^{ad}$ measurable functions $f_1,\dots,f_m:\mathbb R^d\to[-1,1]$ such that
--
--   1. for every $i$ there is a halfspace $h_i\in\mathcal H_d$ with $\mathbb E_{x\sim\mu^{\otimes d}}[f_i(x)h_i(x)]\ge b/\tau$;
--   2. for all $i\ne j$,
--   $$
--   \big|\mathbb E_{x\sim\mu^{\otimes d}}[f_i(x)f_j(x)]\big|\le e^{-b\tau^2}.
--   $$
--
--   The family is the hard instance of the mission: by Lemma 4.5 the matrix with columns $f_i$ is an extractor, and by item 1 it is close to the learning matrix of halfspaces, so Theorem 3.1 applies.
--
--   Differences from the source:
--   - generalization: "c₂ > 0 is a small enough constant", "c₁ > 0 is a sufficiently large constant", Ω-constants, all stated after µ → c₁, c₂, a, b chosen before µ, d and τ; reason: the proof's constants are universal (p.17, "c, c′ > 0 are universal constants"); the uniform statement specializes to the printed one
--   - encoding: m = 2^{Ω(d)}, ≥ Ω(1/τ), ≤ e^{−Ω(τ²)} → 2^{a·d} ≤ m, b/τ ≤ …, … ≤ exp(−b·τ²) with one b; reason: Ω means some positive constant; two constants reduce to their minimum
--   - generalization: functions f_i : ℝ^d → [−1,1] → additionally Measurable (f i); reason: an extra conclusion; the constructed sines are continuous
--   - encoding: halfspace h_i ∈ H_d valued ±1; "f_i, …, f_m" → ∃ w with Σ w_j² = 1 and h_i = sgn ∘ halfspace w; f indexed by Fin m; reason: Lean conventions; "f_i" is a typo for f₁
-- source:
--   S. Garg, T. Jadhav, Memory-Sample Tradeoffs for Agnostically Learning Halfspaces, STOC 2027 submission (manuscript, PDF sha256 386bc9b3…43f84d5), Lemma 4.7, p.13 (proof pp.13–17)

import Mathlib
import Definitions.Def_AgnHalfMem_halfspace
import Definitions.Def_AgnHalfMem_halfVarRadius

open MeasureTheory ProbabilityTheory

namespace AgnHalfMem

/-- **Lemma 4.7 (a large family of nearly orthogonal functions correlated with halfspaces).**
S. Garg, T. Jadhav, *Memory-Sample Tradeoffs for Agnostically Learning Halfspaces*, STOC 2027
submission (manuscript, PDF sha256 386bc9b3…43f84d5), Lemma 4.7, p.13: "Let µ be a distribution
over ℝ with finite non-zero variance σ² > 0 and half-variance radius 1 ≤ Lµ ≤ c₂√d, where c₂ > 0
is a small enough constant. Let τ ∈ [c₁, √d/(4Lµ)], where c₁ > 0 is a sufficiently large constant.
Then there exists a family of m = 2^{Ω(d)} functions f₁, …, f_m : ℝ^d → [−1, 1] such that
1. ∀i ∈ [m], there exists a halfspace h_i ∈ H_d such that E_{x∼µ^{⊗d}}[f_i(x)h_i(x)] ≥ Ω(1/τ).
2. ∀i ≠ j ∈ [m], |E_{x∼µ^{⊗d}}[f_i(x)f_j(x)]| ≤ e^{−Ω(τ²)}."

**Formalization Note.** The constants `c₁, c₂` and the `Ω`-constants `a` (for `m ≥ 2^{a d}`) and
`b` (for both `Ω(1/τ)` and `e^{−Ω(τ²)}`) are universal, chosen before `μ` (p.17: "c, c′ > 0 are
universal constants"). The halfspace `h_i` is `x ↦ sign(⟨w, x⟩)` with `Σ wⱼ² = 1`, valued `±1`
via `sgn`. The functions are produced measurable. `1 ≤ L_μ` holds for every such `μ` and is not
assumed. -/
theorem lemma_4_7 :
    ∃ c₁ c₂ a b : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ 0 < a ∧ 0 < b ∧
      ∀ (μ : Measure ℝ), IsProbabilityMeasure μ → MemLp id 2 μ → 0 < variance id μ →
      ∀ (d : ℕ), halfVarRadius μ ≤ c₂ * Real.sqrt d →
      ∀ τ : ℝ, c₁ ≤ τ → τ ≤ Real.sqrt d / (4 * halfVarRadius μ) →
      ∃ m : ℕ, (2 : ℝ) ^ (a * d) ≤ m ∧ ∃ f : Fin m → (Fin d → ℝ) → ℝ,
        (∀ i, Measurable (f i)) ∧ (∀ i x, f i x ∈ Set.Icc (-1 : ℝ) 1) ∧
        (∀ i, ∃ w : Fin d → ℝ, ∑ j, w j ^ 2 = 1 ∧
          b / τ ≤ ∫ x, f i x * sgn (halfspace w x) ∂(Measure.pi fun _ : Fin d => μ)) ∧
        (∀ i j, i ≠ j →
          |∫ x, f i x * f j x ∂(Measure.pi fun _ : Fin d => μ)| ≤ Real.exp (-(b * τ ^ 2))) := by sorry

end AgnHalfMem
