-- Prove2me | Theorems.Thm_ChurnServiceMode_lemma_5_props_1_5
-- name    : ChurnServiceMode.lemma_5_props_1_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:52:56.966276+00:00
-- url     : https://prove2.me/theorems/a66c0862-6677-47c8-847c-99cd33de3d71
-- title:
--   Lemma 5, properties 1–5: limits, sign and monotonicity of $e^{x^2}\mathrm{erfc}(x)$
-- statement:
--   Let $\operatorname{erf}(x)=\frac2{\sqrt\pi}\int_0^xe^{-t^2}dt$ and $\operatorname{erfc}=1-\operatorname{erf}$. Then:
--   1. $e^{x^2}\operatorname{erfc}(x)(1+2x^2)-\frac{2x}{\sqrt\pi}\ge0$ for every real $x$;
--   2. $e^{x^2}\operatorname{erfc}(x)\to0$ as $x\to\infty$;
--   3. $xe^{x^2}\operatorname{erfc}(x)\to\frac1{\sqrt\pi}$ as $x\to\infty$;
--   4. $xe^{x^2}\operatorname{erf}(x)>-\frac1{\sqrt\pi}$ for every real $x$;
--   5. for every real $\alpha$, with $r(x)=(x+\alpha)e^{x^2}\operatorname{erfc}(x)$:
--      - (i) if $\alpha>0$, $r$ is first strictly increasing and then strictly decreasing on $(-\alpha,\infty)$; if $\alpha\le0$, $r$ is strictly increasing on $(-\alpha,\infty)$;
--      - (ii) for every $0<\beta<1$, the equation $r(x)=\beta/\sqrt\pi$ has a root $x_0>-\alpha$, with $r<\beta/\sqrt\pi$ on $(-\alpha,x_0)$ and $r>\beta/\sqrt\pi$ on $(x_0,\infty)$ (so the root is unique);
--      - (iii) if $\alpha=0$, $r(x)<1/\sqrt\pi$ for every $x$;
--      - (iv) $e^{x^2}\operatorname{erfc}(x)$ is strictly decreasing.
--
--   Property 5(ii) is the analytic core of Lemma 2 (uniqueness of $\theta_b$); the others are used in the verification of Proposition 3.
--
--   **Formalization Note** "First increasing then decreasing" is: there is $m>-\alpha$ with $r$ strictly increasing on $(-\alpha,m]$ and strictly decreasing on $[m,\infty)$.
--
--   Differences from the source:
--   - reading: "increasing", "decreasing", "first increasing then decreasing" (5(i), 5(iv)) → strict monotonicity (StrictMonoOn / StrictAntiOn / StrictAnti); turning point m > −α; reason: the functions are real-analytic and non-constant on the intervals, so weak and strict monotonicity coincide; the strict reading is not weaker
--   - encoding: 5(ii): a unique root x₀ with the stated sign pattern → ∃ x₀ > −α with r x₀ = β/√π and the two sign conditions; reason: the sign conditions imply uniqueness; same content
-- source:
--   Y. Kanoria, I. Lobel, J. Lu, Managing Customer Churn via Service Mode Control, SSRN 3188226 (version of December 1, 2022), https://ssrn.com/abstract=3188226, Lemma 5, properties 1–5, p.18 (PDF p.18)

import Mathlib
import Definitions.Def_ChurnServiceMode_Params

open PSOutsourcing.PartialObs (erf)
open Filter
open scoped Topology

namespace ChurnServiceMode

/-- **Lemma 5, properties 1–5** (Kanoria, Lobel & Lu, *Managing Customer Churn via Service Mode Control*, SSRN 3188226 (Dec 1, 2022), p.18). With `erf(x) = (2/√π)∫₀ˣ e^{−t²}dt` and
`erfc = 1 − erf`:
1. `e^{x²} erfc(x)(1 + 2x²) − 2x/√π ≥ 0` for all real `x`;
2. `e^{x²} erfc(x) → 0` as `x → ∞`;
3. `x e^{x²} erfc(x) → 1/√π` as `x → ∞`;
4. `x e^{x²} erf(x) > −1/√π` for all real `x`;
5. for every real `α`, with `r(x) = (x + α) e^{x²} erfc(x)`:
   (i) if `α > 0`, `r` is first (strictly) increasing then (strictly) decreasing on `(−α, ∞)`;
   if `α ≤ 0`, `r` is (strictly) increasing on `(−α, ∞)`;
   (ii) for every `0 < β < 1`, `r(x) = β/√π` has a root `x₀ > −α` with `r < β/√π` on `(−α, x₀)`
   and `r > β/√π` on `(x₀, ∞)` (so the root is unique);
   (iii) if `α = 0`, `r(x) < 1/√π` for every `x`;
   (iv) `e^{x²} erfc(x)` is (strictly) decreasing.

**Formalization Note.** "Increasing/decreasing" is read strictly; the functions are analytic and
non-constant on the intervals concerned, so the weak and strict readings coincide. -/
theorem lemma_5_props_1_5 :
    (∀ x : ℝ, 0 ≤ Real.exp (x ^ 2) * erfc x * (1 + 2 * x ^ 2) - 2 * x / Real.sqrt Real.pi) ∧
    Tendsto (fun x : ℝ => Real.exp (x ^ 2) * erfc x) atTop (𝓝 0) ∧
    Tendsto (fun x : ℝ => x * Real.exp (x ^ 2) * erfc x) atTop (𝓝 (1 / Real.sqrt Real.pi)) ∧
    (∀ x : ℝ, -(1 / Real.sqrt Real.pi) < x * Real.exp (x ^ 2) * erf x) ∧
    (∀ α : ℝ,
      let r : ℝ → ℝ := fun x => (x + α) * Real.exp (x ^ 2) * erfc x
      ((0 < α → ∃ m : ℝ, -α < m ∧ StrictMonoOn r (Set.Ioc (-α) m) ∧
          StrictAntiOn r (Set.Ici m)) ∧
        (α ≤ 0 → StrictMonoOn r (Set.Ioi (-α)))) ∧
      (∀ β : ℝ, 0 < β → β < 1 → ∃ x₀ : ℝ, -α < x₀ ∧ r x₀ = β / Real.sqrt Real.pi ∧
          (∀ x ∈ Set.Ioo (-α) x₀, r x < β / Real.sqrt Real.pi) ∧
          (∀ x : ℝ, x₀ < x → β / Real.sqrt Real.pi < r x)) ∧
      (α = 0 → ∀ x : ℝ, r x < 1 / Real.sqrt Real.pi)) ∧
    StrictAnti (fun x : ℝ => Real.exp (x ^ 2) * erfc x) := by sorry

end ChurnServiceMode
