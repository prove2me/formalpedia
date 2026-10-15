-- Prove2me | Theorems.Thm_BreakingSample_Perturbed_lemma_5
-- name    : BreakingSample.Perturbed.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:06:09.467251+00:00
-- url     : https://prove2.me/theorems/8a3ba409-8fb6-4557-a7c6-a8f3d0b083fd
-- title:
--   Lemma 5 — planning error under a separated empirical optimum
-- statement:
--   Let $0<\omega<1$ and $\delta>0$. If the empirical model has the separation event $B_\omega$ with probability at least $1-\delta$, then for a universal $c_0>0$ and $N\ge c_0\log(|S||A|/((1-\gamma)\delta\omega))/(1-\gamma)$, both estimates (44) hold with probability at least $1-3\delta$ for every optimal empirical policy. In particular,
--
--   $$\|\widehat V^{\widehat\pi^\star}-V^{\widehat\pi^\star}\|_\infty\le 6\sqrt{\frac{2\log(32|S||A|/((1-\gamma)^3\omega\delta))}{N(1-\gamma)^3}},$$
--   $$V^\star-V^{\widehat\pi^\star}\le 12\sqrt{\frac{2\log(32|S||A|/((1-\gamma)^3\omega\delta))}{N(1-\gamma)^3}}\,\mathbf1.$$
--
--   The lemma transfers concentration to an empirical optimizer when the selected actions are separated.
--
--   **Formalization Note** Rewards lie in $[0,1]$ as in the section setting, and the state set is nonempty. The probability statement bounds the failure event.
-- source:
--   arXiv:2005.12900v8, Lemma 5, (44), p. 17

import Mathlib
import Definitions.Def_BreakingSample_Perturbed_Model
import Definitions.Def_BreakingSample_Perturbed_Sampling
import Definitions.Def_BreakingSample_Perturbed_Absorbing

namespace BreakingSample.Perturbed

/-- Lemma 5 and (44), arXiv:2005.12900v8, p. 17. -/
theorem lemma_5 :
    ∃ c₀ : ℝ, 0 < c₀ ∧
    ∀ (S A : Type) [Fintype S] [DecidableEq S] [Nonempty S] [Fintype A] [DecidableEq A]
      [Nonempty A] (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ),
      IsDiscountedMDP P r γ →
    ∀ (ω δ : ℝ) (N : ℕ), 0 < ω → ω < 1 → 0 < δ → 0 < N →
      sampleProb P N (fun x => ¬ IsSeparated (empKernel x) r γ ω) ≤ δ →
      c₀ * Real.log ((Fintype.card S : ℝ) * Fintype.card A /
        ((1 - γ) * δ * ω)) / (1 - γ) ≤ (N : ℝ) →
      sampleProb P N (fun x => ¬ ∀ π : S → A,
        IsOptimal (empKernel x) r γ π →
          ‖(fun s => value (empKernel x) r γ π s - value P r γ π s)‖ ≤
            6 * Real.sqrt (2 * Real.log
              (32 * Fintype.card S * Fintype.card A /
                ((1 - γ) ^ 3 * ω * δ)) / (N * (1 - γ) ^ 3)) ∧
          ∀ s, optValue P r γ s - value P r γ π s ≤
            12 * Real.sqrt (2 * Real.log
              (32 * Fintype.card S * Fintype.card A /
                ((1 - γ) ^ 3 * ω * δ)) / (N * (1 - γ) ^ 3))) ≤
        3 * δ := by sorry

end BreakingSample.Perturbed
