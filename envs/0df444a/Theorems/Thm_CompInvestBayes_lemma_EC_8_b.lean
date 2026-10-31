-- Prove2me | Theorems.Thm_CompInvestBayes_lemma_EC_8_b
-- name    : CompInvestBayes.lemma_EC_8_b
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:04:39.533993+00:00
-- url     : https://prove2.me/theorems/1b85a81e-0458-45e8-b2b4-42059e85a113
-- title:
--   Lemma EC.8(b) (corrected: at $y_0=c_1\lambda$ the maximizer of $H_0$ is not unique) — the unconstrained maximizer of $H_0$
-- statement:
--   Let the standing assumptions hold and $y_0\in[0,1]$. Over leader sizes $S_1\ge0$:
--
--   1. if $y_0>c_1\lambda$, $\mu_{1,H}$ is the unique maximizer of $H_0(\cdot,y_0)$;
--   2. if $y_0<c_1\lambda$, $\mu_{1,L}$ is the unique maximizer;
--   3. if $y_0=c_1\lambda$, $\mu_{1,L}$ is a maximizer.
--
--   The paper writes $\arg\max_{S_1\ge0}H_0(S_1,y_0)=\mu_{1,L}$ for $y_0\le c_1\lambda$. At $y_0=c_1\lambda$ the slope of $H_0(\cdot,y_0)$ on $(\mu_{1,L},\mu_{1,H}]$ is $y_0/\lambda-c_1=0$, so every $S_1\in[\mu_{1,L},\mu_{1,H}]$ maximizes; for example $H_0(\mu_{1,L},c_1\lambda)=H_0(\mu_{1,H},c_1\lambda)=(1/\lambda-c_1)\mu_{1,L}$.
--
--   Differences from the source:
--   - correction: argmax_{S₁≥0} H₀(S₁, y₀) = µ_{1,L} if y₀ ≤ c₁λ → µ_{1,L} is the unique maximizer for y₀ < c₁λ and a maximizer at y₀ = c₁λ; reason: at y₀ = c₁λ, H₀(µ_{1,L}, c₁λ) = H₀(µ_{1,H}, c₁λ) = (1/λ − c₁)µ_{1,L} with µ_{1,L} ≠ µ_{1,H}, so the argmax is not the single point µ_{1,L}
--   - reading: 'the unconstrained optimizer' (an argmax) → unique maximizer: H₀(S₁, y₀) < H₀(S*, y₀) for every S₁ ≥ 0 with S₁ ≠ S*; reason: the paper writes argmax as a single point
-- source:
--   Sunar, Yu, Kulkarni, Competitive Investment with Bayesian Learning: Choice of Business Size and Timing, SSRN 3408260 (submitted version), Lemma EC.8(b), p.ec21 (PDF 53)

import Mathlib
import Definitions.Def_CompInvestBayes_closedForms

namespace CompInvestBayes

/-- **Lemma EC.8(b)** (SSRN 3408260, p.ec21, PDF 53), corrected at `y₀ = c₁λ`. For a given belief
`y₀ ∈ [0, 1]`, the maximizer of `H₀(·, y₀)` over `S₁ ≥ 0` is
1. `µ_{1,H}`, uniquely, if `y₀ > c₁λ`;
2. `µ_{1,L}`, uniquely, if `y₀ < c₁λ`;
3. `µ_{1,L}` (not uniquely: every `S₁ ∈ [µ_{1,L}, µ_{1,H}]` maximizes) if `y₀ = c₁λ`. -/
theorem lemma_EC_8_b (p : Params) (hp : p.Standing) {y0 : ℝ} (hy0 : y0 ∈ Set.Icc (0 : ℝ) 1) :
    (p.c1 * p.lam < y0 → ∀ S1 : ℝ, 0 ≤ S1 → S1 ≠ p.mu1H → H0 p S1 y0 < H0 p p.mu1H y0) ∧
      (y0 < p.c1 * p.lam → ∀ S1 : ℝ, 0 ≤ S1 → S1 ≠ p.mu1L → H0 p S1 y0 < H0 p p.mu1L y0) ∧
      (y0 = p.c1 * p.lam → ∀ S1 : ℝ, 0 ≤ S1 → H0 p S1 y0 ≤ H0 p p.mu1L y0) := by sorry

end CompInvestBayes
