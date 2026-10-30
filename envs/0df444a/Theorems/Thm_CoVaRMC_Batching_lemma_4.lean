-- Prove2me | Theorems.Thm_CoVaRMC_Batching_lemma_4
-- name    : CoVaRMC.Batching.lemma_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:08:54.316902+00:00
-- url     : https://prove2.me/theorems/59932ca8-81f3-4b87-b5b1-5fe6e37154cd
-- title:
--   Lemma 4, p. 10 — Berry–Esseen: sup_t |Pr{√k/σ̂(y) (F̂_k(y) − E[I{Ŷ ≤ y}]) ≤ t} − Φ(t)| ≤ 33/(4σ̂³(y)k^{1/2})
-- statement:
--   Let $(X_{i,j}, Y_{i,j})$ be i.i.d. with joint density $f$, $\alpha \in (0,1)$, $k, m \ge 1$, and let $\hat Y_1,\dots,\hat Y_k$ be the batch values, $\hat F_k$ their empirical distribution function and $\hat\sigma(y) = \sqrt{\mathrm{Var}(I\{\hat Y \le y\})}$. Let $\Phi$ be the standard normal distribution function. For every $y$ with $\hat\sigma(y) > 0$,
--   $$\sup_{t \in \mathbb R}\left|\Pr\left\{\frac{\sqrt k}{\hat\sigma(y)}\Big(\hat F_k(y) - \mathrm E\big[I\{\hat Y \le y\}\big]\Big) \le t\right\} - \Phi(t)\right| \le \frac{33}{4}\cdot\frac{1}{\hat\sigma^3(y)\,k^{1/2}}.$$
--
--   This controls the across-batch error of (5) uniformly in $t$ and is what lets the proof of Theorem 3 pass from probabilities to the normal distribution function at a rate $k^{-1/2}$.
--
--   **Formalization Note.** Two departures from the page, both disclosed. (1) The hypothesis $\hat\sigma(y) > 0$ is added: the page divides by $\hat\sigma^3(y)$, and in Lean $a/0 = 0$ would make the bound false when $\hat\sigma(y) = 0$. (2) Assumption 1, stated on the page, is not used by the Berry–Esseen argument and is omitted, which strengthens the lemma. The constant $33/4$ is the page's. The supremum over $t$ is written as "for every $t$". $\Phi$ is the distribution function of `gaussianReal 0 1`.
-- source:
--   Huang, Lin, Hong, Monte-Carlo Estimation of CoVaR, arXiv:2210.06148v1, p. 10, Lemma 4

import Mathlib
import Definitions.Def_CoVaRMC_Batching_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace CoVaRMC.Batching

/-- Lemma 4, p. 10 (Berry–Esseen): for `σ̂(y) > 0`,
`sup_t |Pr{(√k / σ̂(y)) (F̂_k(y) - E[I{Ŷ ≤ y}]) ≤ t} - Φ(t)| ≤ (33/4) · 1 / (σ̂³(y) k^{1/2})`. -/
theorem lemma_4 (D : JointDensity) (α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : ℕ × ℕ → Ω → ℝ × ℝ) (hSm : ∀ p, Measurable (S p)) (hSi : iIndepFun S P)
    (hSl : ∀ p, P.map (S p) = D.law)
    (k m : ℕ) (hk : 0 < k) (hm : 0 < m) (y : ℝ) (hσ : 0 < sigmaHat P S α m y) (t : ℝ) :
    |(P {ω | √(k : ℝ) / sigmaHat P S α m y * (FkHat S α k m y ω - pHat P S α m y) ≤ t}).toReal
        - cdf (gaussianReal 0 1) t|
      ≤ 33 / 4 * (1 / (sigmaHat P S α m y ^ 3 * √(k : ℝ))) := by sorry

end CoVaRMC.Batching
