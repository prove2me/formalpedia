-- Prove2me | Theorems.Thm_AgnHalfMem_claim_4_9
-- name    : AgnHalfMem.claim_4_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:14:06.624052+00:00
-- url     : https://prove2.me/theorems/849ed3be-706d-40e2-8d2c-56cc33ca31fb
-- title:
--   Claim 4.9 — near-orthogonality of sine functions, $|\mathbb E[f_vf_{v'}]|\le e^{-\tau^2/80}$
-- statement:
--   Let $\mu$ be a probability measure on $\mathbb R$ with finite non-zero variance, half-variance radius $L_\mu$ and normalized difference law $\mu'$. Let $s\in\mathbb N$ and $\tau\ge0$ with $2\tau L_\mu\le\sqrt s$. Let $v,v'\in\mathbb R^s$ be such that both sets
--   $$
--   H_+=\Big\{j:\tfrac1{\sqrt s}\le|v_j+v'_j|\le\tfrac2{\sqrt s}\Big\},\qquad H_-=\Big\{j:\tfrac1{\sqrt s}\le|v_j-v'_j|\le\tfrac2{\sqrt s}\Big\}
--   $$
--   have at least $s/10$ elements. Then
--   $$
--   \Big|\mathbb E_{z\sim\mu'^{\otimes s}}\big[\sin(\tau\langle v,z\rangle)\sin(\tau\langle v',z\rangle)\big]\Big|\ \le\ e^{-\tau^2/80}.
--   $$
--
--   This gives the near-orthogonality half of Lemma 4.7: random Gaussian directions are pairwise in the position required here, so their sine functions are almost uncorrelated under $\mu'^{\otimes s}$.
--
--   Differences from the source:
--   - generalization: claim stated inside the proof of Lemma 4.7 (τ ≤ √d/(4L_µ), d = 2s), conclusion e^{−Ω(τ²)} → every µ with finite non-zero variance, s, τ ≥ 0 with 2τL_µ ≤ √s; conclusion exp(−τ²/80); reason: the proof uses exactly |τu_j| ≤ 2τ/√s ≤ 1/L and obtains the constant 1/80 (p.16); the lemma's context implies 2τL ≤ √s, and the explicit constant implies the Ω form
--   - encoding: µ′^{⊗s}, |H_±| ≥ s/10 → Measure.pi of diffLaw μ; (s:ℝ)/10 ≤ card of the filtered Finset over Fin s; reason: Lean conventions; same instances
-- source:
--   S. Garg, T. Jadhav, Memory-Sample Tradeoffs for Agnostically Learning Halfspaces, STOC 2027 submission (manuscript, PDF sha256 386bc9b3…43f84d5), Claim 4.9, p.15 (proof pp.15–16)

import Mathlib
import Definitions.Def_AgnHalfMem_halfVarRadius
import Definitions.Def_AgnHalfMem_sineFn

open MeasureTheory ProbabilityTheory

namespace AgnHalfMem

/-- **Claim 4.9 (near-orthogonality of sine functions).** S. Garg, T. Jadhav, *Memory-Sample
Tradeoffs for Agnostically Learning Halfspaces*, STOC 2027 submission (manuscript, PDF sha256
386bc9b3…43f84d5), Claim 4.9, p.15: "Let v, v′ ∈ ℝ^s be two s-dimensional vectors such that the
following two sets have size at least s/10: H₊ = {j : 1/√s ≤ |v_j + v′_j| ≤ 2/√s},
H₋ = {j : 1/√s ≤ |v_j − v′_j| ≤ 2/√s}. Then,
|E_{z∼µ′^{⊗s}}[f_v(z) f_{v′}(z)]| = |E_{z∼µ′^{⊗s}}[sin(τ⟨v, z⟩) sin(τ⟨v′, z⟩)]| ≤ e^{−Ω(τ²)}."

**Formalization Note.** The context of the claim inside the proof of Lemma 4.7 is made explicit:
every `μ` with finite non-zero variance, `τ ≥ 0` with `2τ L_μ ≤ √s` (the proof's
"τ/√s ≤ |τu_j| ≤ 2τ/√s ≤ 1/L", p.16; implied by the lemma's `τ ≤ √d/(4L)` with `d = 2s`). The
constant of `e^{−Ω(τ²)}` is the proof's `1/80` (p.16). `µ′` is `diffLaw μ`. -/
theorem claim_4_9 :
    ∀ (μ : Measure ℝ), IsProbabilityMeasure μ → MemLp id 2 μ → 0 < variance id μ →
    ∀ (s : ℕ) (τ : ℝ), 0 ≤ τ → 2 * τ * halfVarRadius μ ≤ Real.sqrt s →
    ∀ v v' : Fin s → ℝ,
      (s : ℝ) / 10 ≤ ((Finset.univ.filter fun j =>
          1 / Real.sqrt s ≤ |v j + v' j| ∧ |v j + v' j| ≤ 2 / Real.sqrt s).card : ℝ) →
      (s : ℝ) / 10 ≤ ((Finset.univ.filter fun j =>
          1 / Real.sqrt s ≤ |v j - v' j| ∧ |v j - v' j| ≤ 2 / Real.sqrt s).card : ℝ) →
      |∫ z, sineFn τ v z * sineFn τ v' z ∂(Measure.pi fun _ : Fin s => diffLaw μ)| ≤
        Real.exp (-(τ ^ 2 / 80)) := by sorry

end AgnHalfMem
