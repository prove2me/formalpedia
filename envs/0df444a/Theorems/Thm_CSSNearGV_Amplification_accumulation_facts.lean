-- Prove2me | Theorems.Thm_CSSNearGV_Amplification_accumulation_facts
-- name    : CSSNearGV.Amplification.accumulation_facts
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T21:18:32.624784+00:00
-- url     : https://prove2.me/theorems/027942f5-5231-48d1-83d6-baf8f9bb1bac
-- title:
--   Proposition 3.6 — accumulation transition entropy
-- statement:
--   On the accumulation transition domain $0\le\alpha\le1$, $\alpha/2\le\gamma\le1-\alpha/2$,
--   $$f_A(\alpha,\gamma)\le0,\qquad f_A(\alpha,\gamma)=0\iff\alpha=0\ \text{or}\ \gamma=1/2.$$
--   It is nonincreasing in $\alpha$, symmetric in $\gamma$ about $1/2$, and nondecreasing in $\gamma\le1/2$. For fixed $0<\gamma<1$, the function $h(\alpha)+f_A(\alpha,\gamma)-h(\gamma)$ is concave on $(0,\min(2\gamma,2(1-\gamma))]$ and has maximum zero at $\lambda_\gamma=2\gamma(1-\gamma)$.
--
--   These properties control the spectral update.
--
--   Differences from the source:
--   - encoding: binary words, finite expectations and feasible entropy maxima → Fin-indexed binary vectors, exact finite averages and domain-restricted extrema; reason: the representation preserves the source objects and domains; endpoint values use continuous entropy extensions
--   - reading: increasing and decreasing → nondecreasing and nonincreasing; reason: f_A(0,gamma)=0 and f_A(alpha,1/2)=0 have flat sections, so strict monotonicity would contradict the equality cases in the source
-- source:
--   Rachel Yun Zhang, Linear-Time Encodable Quantum Codes near the CSS GV Bound, STOC 2027 submission #1164 (October 2026), Proposition 3.6, printed p.12 / PDF 14; proof printed pp.28–29 / PDF 30–31

import Definitions.Def_CSSNearGV_Amplification_Estimates

open scoped BigOperators
noncomputable section

namespace CSSNearGV.Amplification

theorem accumulation_facts :
  (∀ α γ : ℝ, domainA α γ → fA α γ ≤ 0 ∧ (fA α γ = 0 ↔ α = 0 ∨ γ = 1 / 2)) ∧
  (∀ α₁ α₂ γ : ℝ, domainA α₁ γ → domainA α₂ γ → α₁ ≤ α₂ → fA α₂ γ ≤ fA α₁ γ) ∧
  (∀ α γ : ℝ, domainA α γ → fA α (1 - γ) = fA α γ) ∧
  (∀ α γ₁ γ₂ : ℝ, domainA α γ₁ → domainA α γ₂ → γ₁ ≤ γ₂ → γ₂ ≤ 1 / 2 → fA α γ₁ ≤ fA α γ₂) ∧
  (∀ γ ∈ Set.Ioo (0 : ℝ) 1,
    ConcaveOn ℝ (Set.Ioc 0 (min (2 * γ) (2 * (1 - γ))))
      (fun α => entropy α + fA α γ - entropy γ) ∧
    (∀ α ∈ Set.Ioc (0 : ℝ) (min (2 * γ) (2 * (1 - γ))), entropy α + fA α γ - entropy γ ≤ 0) ∧
    entropy (lambda γ) + fA (lambda γ) γ - entropy γ = 0) := by sorry

end CSSNearGV.Amplification
