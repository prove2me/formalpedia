-- Prove2me | Theorems.Thm_ChurnServiceMode_lemma_5_props_6_8
-- name    : ChurnServiceMode.lemma_5_props_6_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:52:44.78762+00:00
-- url     : https://prove2.me/theorems/8e86bde5-8132-4b0c-a299-7e555149be59
-- title:
--   Lemma 5, properties 6–8: root bound, monotone combination, log-convexity
-- statement:
--   With $\operatorname{erfc}=1-\operatorname{erf}$:
--   1. (Property 6) if $\alpha>0$ and $0<\beta<1$, the root $x_0>-\alpha$ of $(x+\alpha)e^{x^2}\operatorname{erfc}(x)=\beta/\sqrt\pi$ (property 5(ii)) satisfies
--   $$x_0\le\frac{\alpha(\beta-2)+\sqrt{\alpha^2\beta^2+2\beta(1-\beta)}}{2(1-\beta)};$$
--   2. (Property 7) for every constant $C\in[-1,1]$, the function $x\mapsto\frac{C}{\sqrt\pi}+xe^{x^2}\bigl(1+C\operatorname{erf}(x)\bigr)$ is non-decreasing;
--   3. (Property 8) the derivative of $F(x)=\log\bigl(xe^{x^2}\operatorname{erfc}(-x)+\frac1{\sqrt\pi}\bigr)$ is strictly increasing.
--
--   These inequalities are used in the proof of Proposition 3 to verify the HJB inequality (14) for the candidate value function.
--
--   **Formalization Note** The argument of the logarithm in property 8 is positive for every $x$ by property 5(iii), so $F$ is a genuine logarithm.
--
--   Differences from the source:
--   - encoding: property 6: "x₀ defined in property 5(ii)" → every x₀ > −α with (x₀+α)e^{x₀²}erfc(x₀) = β/√π; reason: by 5(ii) there is exactly one such x₀; same content
--   - reading: property 8: "is increasing" → StrictMono (deriv F); reason: F′ is real-analytic and not constant (F′(x) ~ 2x), so weak and strict monotonicity coincide; the strict reading is not weaker
-- source:
--   Y. Kanoria, I. Lobel, J. Lu, Managing Customer Churn via Service Mode Control, SSRN 3188226 (version of December 1, 2022), https://ssrn.com/abstract=3188226, Lemma 5, properties 6–8, p.18 (PDF p.18); proofs OA A, PDF pp.36–40

import Mathlib
import Definitions.Def_ChurnServiceMode_Params

open PSOutsourcing.PartialObs (erf)

namespace ChurnServiceMode

/-- **Lemma 5, properties 6–8** (Kanoria, Lobel & Lu, *Managing Customer Churn via Service Mode Control*, SSRN 3188226 (Dec 1, 2022), p.18). With `erfc = 1 − erf`:
6. if `α > 0` and `0 < β < 1`, the root `x₀ > −α` of `(x + α) e^{x²} erfc(x) = β/√π` of property
   5(ii) satisfies `x₀ ≤ (α(β − 2) + √(α²β² + 2β(1 − β)))/(2(1 − β))`;
7. for every constant `C ∈ [−1, 1]`, `C/√π + x e^{x²}(1 + C erf(x))` is non-decreasing in `x`;
8. the derivative of `F(x) = log(x e^{x²} erfc(−x) + 1/√π)` is (strictly) increasing.

**Formalization Note.** Property 6 is stated for every `x₀ > −α` solving the equation (property
5(ii) says there is exactly one). In property 8 the argument of `log` is positive by property
5(iii), so `F` is the true logarithm; "increasing" is read strictly (`F′` is analytic and not
constant). -/
theorem lemma_5_props_6_8 :
    (∀ α β : ℝ, 0 < α → 0 < β → β < 1 → ∀ x₀ : ℝ, -α < x₀ →
      (x₀ + α) * Real.exp (x₀ ^ 2) * erfc x₀ = β / Real.sqrt Real.pi →
      x₀ ≤ (α * (β - 2) + Real.sqrt (α ^ 2 * β ^ 2 + 2 * β * (1 - β))) / (2 * (1 - β))) ∧
    (∀ C : ℝ, C ∈ Set.Icc (-1 : ℝ) 1 →
      Monotone (fun x : ℝ => C / Real.sqrt Real.pi + x * Real.exp (x ^ 2) * (1 + C * erf x))) ∧
    StrictMono (deriv (fun x : ℝ =>
      Real.log (x * Real.exp (x ^ 2) * erfc (-x) + 1 / Real.sqrt Real.pi))) := by sorry

end ChurnServiceMode
