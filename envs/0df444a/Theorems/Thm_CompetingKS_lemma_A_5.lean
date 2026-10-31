-- Prove2me | Theorems.Thm_CompetingKS_lemma_A_5
-- name    : CompetingKS.lemma_A_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:17:40.809251+00:00
-- url     : https://prove2.me/theorems/3088efe8-a093-4f57-ba0a-6d57fe83f67e
-- title:
--   Lemma A.5 — NB and KS best responses (40)–(41) in the two-to-one channel, with the root of (42)
-- statement:
--   Consider the two-to-one channel with $a=b=1$, $c=0$, and let $\eta\in[0,1)$. For $\theta\in[0,1]$ put
--   $$
--   t_1=1-\frac{\eta(1+\theta)}{2-\eta^2(1-\theta)},\qquad t_2=1-\frac{\eta(1+\theta)-\eta^3(1-\theta)}{2(1-\eta^2(1-\theta))},
--   $$
--   and let
--   $$
--   \Phi(w_i,w_j)=-2w_i^3+(5-\theta)w_i^2-2\bigl(1+(1-\theta)(2w_j-w_j^2)\bigr)w_i+(1-\theta)(2w_j-w_j^2).
--   $$
--   For $w_j\in[0,1]$ the unique Nash bargaining response of unit $i$ to $w_j$ is
--   $$
--   w_i^{NB}(w_j)=\begin{cases}\frac{(1-\theta)(1-\eta+\eta w_j)}2&w_j<t_1,\\[2pt]\frac{\eta-1+w_j}\eta&t_1<w_j<t_2,\\[2pt]w_i^\alpha(w_j)&w_j>t_2,\end{cases}
--   $$
--   where, for $w_j>t_2$, $\Phi(\cdot,w_j)$ has a unique root $w_i^\alpha(w_j)$ in $[0,\frac12]$.
--
--   Put $N=(1-\eta)^2+2(4+\eta-5\eta^2)w_j-(4-5\eta^2)w_j^2$, $t_3=\frac{(2+\eta)(1-\eta)}{2-\eta^2}$, and let $\Delta_1,\Delta_2$ be the polynomials in $w_j$ of the source's Lemma A.5. There is a threshold $\bar w^c\in[1-\eta,t_3]$ such that for $w_j\in[0,1]$ the unique Kalai–Smorodinsky response of unit $i$ to $w_j$ is
--   $$
--   w_i^{KS}(w_j)=\begin{cases}\frac{1-\eta+\eta w_j}5&w_j<1-\eta,\\[2pt]\frac{(1-\eta+\eta w_j)^3}{N}&1-\eta<w_j<\bar w^c,\\[2pt]\frac{(1-\eta)^2+2(2+\eta-3\eta^2)w_j-(2-3\eta^2)w_j^2-\sqrt{\Delta_1}}{N}&\bar w^c<w_j<t_3,\\[2pt]1+\frac{\eta^2(2w_j-w_j^2)+\sqrt{\Delta_2}}{2(1-\eta-(2-\eta+2\eta^2)w_j+(1+\eta^2)w_j^2)}&t_3<w_j<\frac{2-\eta}2,\\[2pt]\frac{1+4w_j-2w_j^2-\sqrt{1+6w_j-3w_j^2}}{1+8w_j-4w_j^2}&w_j>\frac{2-\eta}2.\end{cases}
--   $$
--
--   These are the best-response maps of the two-to-one channel; the equilibria of Proposition 2 are their mutual fixed points.
--
--   **Formalization Note** The middle range of the first display is empty at $\eta=0$. The polynomials are `Delta1`, `Delta2` and the cubic is `Phi`, from `CompetingKS.unitOT`.
--
--   Differences from the source:
--   - encoding: contracts wᵢ with no stated range in the appendix → contracts w ∈ [0, 1], and the printed strict ranges of wⱼ inside [0, 1]; reason: [c, a] is the paper's contract space (p.15), which normalizes to [0, 1]
--   - reading: the negotiated price is x → for every w, w is a response if and only if w = x; reason: existence and uniqueness of the response is what "the negotiated price" asserts; the stronger reading
--   - reading: the KS solution as equation (2) on a non-convex allocation set → individual rationality, Pareto optimality and (2) cross-multiplied; reason: the paper restricts (2) to Pareto allocations (online appendix p.5, pp.14–15); without Pareto every contract with allocation (D, d) satisfies (2) as 0 = 0
--   - encoding: η ∈ [0, 1] for the two-to-one channel → η ∈ [0, 1); reason: at η = 1, wᵢ = wⱼ < a Lemma 1(ii)(a) gives q*ᵢ = 0 and (ii)(c) gives q*ᵢ = (a − wᵢ)/(2b), and (ii)(b) divides by 1 − η² = 0, so q* and the profits are undefined there; this excludes only that undefined case
--   - reading: "w̄ᶜⱼ is some value" → w̄ᶜ depends on η only and is quantified before wⱼ; reason: a threshold in wⱼ cannot depend on wⱼ
-- source:
--   Feng, Li, Shanthikumar, Negotiations in Competing Supply Chains: The Kalai-Smorodinsky Bargaining Solution, accepted manuscript (Management Science, July 3, 2021), SSRN 3447674, Lemma A.5, online appendix p.10, with (42), online appendix p.11

import Mathlib
import Definitions.Def_CompetingKS_unitOT

namespace CompetingKS

/-- Lemma A.5, Feng, Li, Shanthikumar, *Negotiations in Competing Supply Chains: The
Kalai-Smorodinsky Bargaining Solution*, accepted manuscript (Management Science, July 3, 2021),
SSRN 3447674, online appendix p.10, with (42), online appendix p.11: the NB best response (40) and
the KS best response (41) of unit `i` of the normalized two-to-one channel to a contract
`wⱼ ∈ [0, 1]`.

**Formalization Note** `η ∈ [0, 1)`. "The negotiated price is `x`" is `∀ w, response w ↔ w = x`:
the response exists and is unique. On the third range of (40) the root `w^α_i(wⱼ)` of (42) in
`[0, 1/2]` exists and is unique, and it is the response. The threshold `w̄ᶜⱼ` (for each `η`) is
existential, in the printed interval, and quantified before `wⱼ`. The ranges are strict, as printed;
the middle range of (40) is empty at `η = 0`, so its division by `η` is harmless. -/
theorem lemma_A_5 {η : ℝ} (hη₀ : 0 ≤ η) (hη₁ : η < 1) :
    (∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → ∀ wj ∈ Set.Icc (0 : ℝ) 1,
      (wj < 1 - η * (1 + θ) / (2 - η ^ 2 * (1 - θ)) →
        ∀ w, (normTO η wj).IsNBResponse θ w ↔ w = (1 - θ) * (1 - η + η * wj) / 2) ∧
      (1 - η * (1 + θ) / (2 - η ^ 2 * (1 - θ)) < wj →
        wj < 1 - (η * (1 + θ) - η ^ 3 * (1 - θ)) / (2 * (1 - η ^ 2 * (1 - θ))) →
        ∀ w, (normTO η wj).IsNBResponse θ w ↔ w = (η - 1 + wj) / η) ∧
      (1 - (η * (1 + θ) - η ^ 3 * (1 - θ)) / (2 * (1 - η ^ 2 * (1 - θ))) < wj →
        (∃! x : ℝ, x ∈ Set.Icc (0 : ℝ) (1 / 2) ∧ Phi θ x wj = 0) ∧
        ∀ x ∈ Set.Icc (0 : ℝ) (1 / 2), Phi θ x wj = 0 →
          ∀ w, (normTO η wj).IsNBResponse θ w ↔ w = x)) ∧
    (∃ wc : ℝ, 1 - η ≤ wc ∧ wc ≤ (2 + η) * (1 - η) / (2 - η ^ 2) ∧
      ∀ wj ∈ Set.Icc (0 : ℝ) 1,
        (wj < 1 - η → ∀ w, (normTO η wj).IsKSResponse w ↔ w = (1 - η + η * wj) / 5) ∧
        (1 - η < wj → wj < wc → ∀ w, (normTO η wj).IsKSResponse w ↔
          w = (1 - η + η * wj) ^ 3 /
            ((1 - η) ^ 2 + 2 * (4 + η - 5 * η ^ 2) * wj - (4 - 5 * η ^ 2) * wj ^ 2)) ∧
        (wc < wj → wj < (2 + η) * (1 - η) / (2 - η ^ 2) →
          ∀ w, (normTO η wj).IsKSResponse w ↔
            w = ((1 - η) ^ 2 + 2 * (2 + η - 3 * η ^ 2) * wj - (2 - 3 * η ^ 2) * wj ^ 2 -
                √(Delta1 η wj)) /
              ((1 - η) ^ 2 + 2 * (4 + η - 5 * η ^ 2) * wj - (4 - 5 * η ^ 2) * wj ^ 2)) ∧
        ((2 + η) * (1 - η) / (2 - η ^ 2) < wj → wj < (2 - η) / 2 →
          ∀ w, (normTO η wj).IsKSResponse w ↔
            w = 1 + (η ^ 2 * (2 * wj - wj ^ 2) + √(Delta2 η wj)) /
              (2 * (1 - η - (2 - η + 2 * η ^ 2) * wj + (1 + η ^ 2) * wj ^ 2))) ∧
        ((2 - η) / 2 < wj → ∀ w, (normTO η wj).IsKSResponse w ↔
          w = (1 + 4 * wj - 2 * wj ^ 2 - √(1 + 6 * wj - 3 * wj ^ 2)) /
            (1 + 8 * wj - 4 * wj ^ 2))) := by sorry

end CompetingKS
