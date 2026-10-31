-- Prove2me | Theorems.Thm_CompetingKS_lemma_A_2
-- name    : CompetingKS.lemma_A_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:17:23.867237+00:00
-- url     : https://prove2.me/theorems/59d339ce-972b-47fd-9d20-e45f9c51f01a
-- title:
--   Lemma A.2 — NB and KS best responses (22)–(23) in the one-to-two channel
-- statement:
--   Consider the one-to-two channel with $a=b=1$, $c=0$, and let $\eta\in[0,1]$. Put $w^d=\frac12+\frac12\sqrt{\frac{2-\eta}{2+\eta}}$.
--
--   For every $\theta\in[0,1]$ there is a threshold $\bar w^a\in\bigl[\frac{4-\eta(1+\theta)}{4-\eta^2\theta},\frac{4+\eta(1-\theta)}{2(2+\eta)}\bigr]$ such that for $w_j\in[0,1]$ the unique Nash bargaining response of unit $i$ to $w_j$ is
--   $$
--   w_i^{NB}(w_j)=\begin{cases}\frac{(2-\eta)(1-\theta)+2\eta w_j}4&w_j<\bar w^a,\\[2pt]\frac{3-\theta-\sqrt{(1+\theta)^2-16\theta w_j(1-w_j)}}4&w_j>\bar w^a.\end{cases}
--   $$
--
--   There is a threshold $\bar w^b\in\bigl[\frac2{2+\eta},\frac{4-\eta}4\bigr]$ such that for $w_j\in[0,1]$ the unique Kalai–Smorodinsky response of unit $i$ to $w_j$ is
--   $$
--   w_i^{KS}(w_j)=\begin{cases}\frac{\eta w_j}2+\frac{2-\eta}{10}&w_j<\frac2{2+\eta},\\[2pt]\frac{\eta w_j}2+\frac{2-\eta}{2+2(2+\eta)^2w_j^2}&\frac2{2+\eta}<w_j<\bar w^b,\\[2pt]\frac12-\frac{-2+\eta+4\sqrt{w_j^3(2+\eta)(4w_j-4(2+\eta)w_j^2(1-w_j)-2+\eta)}}{2(2-\eta+4(2+\eta)w_j^2)}&\bar w^b<w_j<w^d,\\[2pt]\frac12-\frac{-(2w_j-1)^2+4\sqrt{w_j^3(2w_j-1)^3}}{2(1-4w_j+8w_j^2)}&w_j>w^d.\end{cases}
--   $$
--
--   These are the best-response maps of the one-to-two channel; the equilibria of Proposition 2 are their mutual fixed points.
--
--   Differences from the source:
--   - encoding: contracts wᵢ with no stated range in the appendix → contracts w ∈ [0, 1], and the printed strict ranges of wⱼ inside [0, 1]; reason: [c, a] is the paper's contract space (p.15), which normalizes to [0, 1]
--   - reading: the negotiated price is x → for every w, w is a response if and only if w = x; reason: existence and uniqueness of the response is what "the negotiated price" asserts; the stronger reading
--   - reading: the KS solution as equation (2) on a non-convex allocation set → individual rationality, Pareto optimality and (2) cross-multiplied; reason: the paper restricts (2) to Pareto allocations (online appendix p.5, pp.14–15); without Pareto every contract with allocation (D, d) satisfies (2) as 0 = 0
--   - reading: "w̄ᵃⱼ is some value", "w̄ᵇⱼ is some value" → w̄ᵃ depends on η, θ only and w̄ᵇ on η only, both quantified before wⱼ; reason: a threshold in wⱼ cannot depend on wⱼ
--   - reading: third piece of (23) ranges over "wᵇⱼ < wⱼ" → w̄ᵇ < wⱼ; reason: the bar is missing on the page; the second piece and the proof use w̄ᵇⱼ
-- source:
--   Feng, Li, Shanthikumar, Negotiations in Competing Supply Chains: The Kalai-Smorodinsky Bargaining Solution, accepted manuscript (Management Science, July 3, 2021), SSRN 3447674, Lemma A.2, online appendix p.4

import Mathlib
import Definitions.Def_CompetingKS_unitOT

namespace CompetingKS

/-- Lemma A.2, Feng, Li, Shanthikumar, *Negotiations in Competing Supply Chains: The
Kalai-Smorodinsky Bargaining Solution*, accepted manuscript (Management Science, July 3, 2021),
SSRN 3447674, online appendix p.4: the NB best response (22) and the KS best response (23) of unit
`i` of the normalized one-to-two channel to a contract `wⱼ ∈ [0, 1]`.

**Formalization Note** "The negotiated price is `x`" is `∀ w, response w ↔ w = x`: the response
exists and is unique. The thresholds `w̄ᵃⱼ` (for each `η`, `θ`) and `w̄ᵇⱼ` (for each `η`) are
existential, in the printed intervals, and quantified before `wⱼ`. "wᵇⱼ" in the third piece of (23)
is `w̄ᵇⱼ`, as in the second piece and in the proof. The ranges are strict, as printed. -/
theorem lemma_A_2 {η : ℝ} (hη₀ : 0 ≤ η) (hη₁ : η ≤ 1) :
    (∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      ∃ wa : ℝ, (4 - η * (1 + θ)) / (4 - η ^ 2 * θ) ≤ wa ∧
        wa ≤ (4 + η * (1 - θ)) / (2 * (2 + η)) ∧
        ∀ wj ∈ Set.Icc (0 : ℝ) 1,
          (wj < wa → ∀ w, (normOT η wj).IsNBResponse θ w ↔
            w = ((2 - η) * (1 - θ) + 2 * η * wj) / 4) ∧
          (wa < wj → ∀ w, (normOT η wj).IsNBResponse θ w ↔
            w = (3 - θ - √((1 + θ) ^ 2 - 16 * θ * wj * (1 - wj))) / 4)) ∧
    (∃ wb : ℝ, 2 / (2 + η) ≤ wb ∧ wb ≤ (4 - η) / 4 ∧
      ∀ wj ∈ Set.Icc (0 : ℝ) 1,
        (wj < 2 / (2 + η) → ∀ w, (normOT η wj).IsKSResponse w ↔
          w = η * wj / 2 + (2 - η) / 10) ∧
        (2 / (2 + η) < wj → wj < wb → ∀ w, (normOT η wj).IsKSResponse w ↔
          w = η * wj / 2 + (2 - η) / (2 + 2 * (2 + η) ^ 2 * wj ^ 2)) ∧
        (wb < wj → wj < 1 / 2 + 1 / 2 * √((2 - η) / (2 + η)) →
          ∀ w, (normOT η wj).IsKSResponse w ↔
            w = 1 / 2 - (-2 + η + 4 * √(wj ^ 3 * (2 + η) *
                (4 * wj - 4 * (2 + η) * wj ^ 2 * (1 - wj) - 2 + η))) /
              (2 * (2 - η + 4 * (2 + η) * wj ^ 2))) ∧
        (1 / 2 + 1 / 2 * √((2 - η) / (2 + η)) < wj →
          ∀ w, (normOT η wj).IsKSResponse w ↔
            w = 1 / 2 - (-(2 * wj - 1) ^ 2 + 4 * √(wj ^ 3 * (2 * wj - 1) ^ 3)) /
              (2 * (1 - 4 * wj + 8 * wj ^ 2)))) := by sorry

end CompetingKS
