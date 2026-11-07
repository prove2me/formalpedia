-- Prove2me | Theorems.Thm_ContinualCounting_lemma_3_noise_accumulation
-- name    : ContinualCounting.lemma_3_noise_accumulation
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:43:11.620705+00:00
-- url     : https://prove2.me/theorems/104d1efc-584b-45ef-9c23-5d5612bd0258
-- title:
--   Lemma 3 — noise accumulates up the tree
-- statement:
--   Let $\nu$ be a probability law of the noise $z$ on $\mathbb R^{2^h}$, and let $u$ be an internal node of $\mathcal T$ whose children are not leaves. Then
--   $$\mathbb E[\max\nolimits^{<u}(z)-\min\nolimits^{<u}(z)]\ge\frac{\sigma_{u,\ell}}2+\frac{\sigma_{u,r}}2+\sum_{f,g\in\{\ell,r\}^2}\frac{\mathbb E[\max\nolimits^{<f(g(u))}(z)-\min\nolimits^{<f(g(u))}(z)]}4.$$
--
--   Recursing on even levels turns this into a lower bound on $\mathbb E\|z\|_\infty$ by a weighted sum of residual noises.
--
--   **Formalization Note** Expectations are `lintegral`s of the nonnegative ranges with values in $[0,\infty]$.
--
--   Differences from the source:
--   - generalization: §5 assumes n is a power of 16, h = log₂ n → every height h, n = 2^h; reason: the statement and its proof use only that the grandchildren of u exist; powers of 16 are the case 4 ∣ h
--   - encoding: σ_{u,ℓ}, σ_{u,r} as E[inf_m E[·|·]] with real values → infimum over measurable predictors, in ℝ≥0∞; reason: the two values coincide, by the smallest conditional median (see `sigmaL`)
-- source:
--   Bairaktari, Dahl, Larsen, The Binary Tree Mechanism is Optimal for Differentially Private Continual Counting, arXiv:2607.00876 (sha256 986e6426…), Lemma 3, p.19 (PDF p.20); proof pp.19–21 (PDF pp.20–22)

import Mathlib
import Definitions.Def_ContinualCounting_belowRange
import Definitions.Def_ContinualCounting_sigmaL

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace ContinualCounting

/-- **Lemma 3 (noise accumulates up the tree).** Bairaktari, Dahl, Larsen, arXiv:2607.00876 (sha256
986e6426…), p.19: "For any internal node u ∈ T whose children are not leaves, we have
E[max^{<u}(z) − min^{<u}(z)] ≥ σ_{u,ℓ}/2 + σ_{u,r}/2 + ∑_{f,g∈{ℓ,r}^2} E[max^{<f(g(u))}(z) − min^{<f(g(u))}(z)]/4."

**Formalization Note.** "Internal node whose children are not leaves" is `d(u) + 2 ≤ h`. The noise law
`ν` is any probability measure on `ℝ^{2^h}`, and every height `h` is allowed. Expectations are
`lintegral`s of the nonnegative ranges. `f, g` run over the two child maps. -/
theorem lemma_3_noise_accumulation {h : ℕ} (ν : Measure (Fin (2 ^ h) → ℝ)) [IsProbabilityMeasure ν]
    (u : Node) (hu : IsNode h u) (hd : u.1 + 2 ≤ h) :
    sigmaL ν u / 2 + sigmaR ν u / 2 +
        ∑ f : Bool, ∑ g : Bool,
          (∫⁻ z, ENNReal.ofReal
            (belowRange h ((if f then right else left) ((if g then right else left) u)) z) ∂ν) / 4
      ≤ ∫⁻ z, ENNReal.ofReal (belowRange h u z) ∂ν := by sorry

end ContinualCounting
