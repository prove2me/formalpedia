-- Prove2me | Theorems.Thm_ExactModKL_lemma_3_8
-- name    : ExactModKL.lemma_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:55:53.831605+00:00
-- url     : https://prove2.me/theorems/70e4e4fc-3caf-4028-bdec-6414293468c7
-- title:
--   Lemma 3.8 — the integral of a nonnegative decreasing $h$ is concave with $\varphi'_-\ge h$, strictly increasing when $h>0$
-- statement:
--   Let $\eta\in(0,\infty]$ and let $h:(0,\eta)\to\mathbb R_+$ be nonnegative and nonincreasing. Define
--   $$
--   \varphi(t)=\int_0^t h(s)\,ds\quad(t\in(0,\eta)),\qquad\varphi(0)=0,
--   $$
--   and suppose that $\varphi(t)<\infty$ for $t\in(0,\eta)$. Then
--
--   1. $\varphi$ is concave and nondecreasing on $[0,\eta)$ and right-continuous at $0$;
--   2. $\varphi'_-(t)\ge h(t)$ for every $t\in(0,\eta)$;
--   3. if $h$ is positive-valued, $\varphi$ is strictly increasing on $[0,\eta)$;
--   4. if $h$ is continuous on $(0,\eta)$, then $\varphi$ is $C^1$ on $(0,\eta)$.
--
--   For positive-valued $h$ this is the printed lemma. It is applied to the function $h$ of Definition 3.6 to show that the exact modulus is concave and desingularizing.
--
--   Differences from the source:
--   - generalization: h positive-valued; conclusion: ϕ strictly increasing concave, ϕ′_− ≥ h, right-continuous at 0, C¹ if h is continuous → h nonnegative; conclusions concavity, monotonicity (weak), right-continuity at 0, ϕ′_− ≥ h unconditionally, strict monotonicity under h > 0 on (0, η), C¹ under continuity of h; reason: positivity is used only for strict monotonicity; with h positive-valued every printed conclusion follows, so the statement specializes to the printed lemma (needed because the h of Definition 3.6 can vanish, paper.md C1)
--   - encoding: ϕ(t) < ∞ for t ∈ (0, η) → h integrable on (0, t] for every t ∈ (0, η); ϕ(t) the Lebesgue integral over (0, t]; reason: for a nonnegative monotone (hence measurable) h, finiteness of ∫_0^t h is integrability
--   - reading: "decreasing", "increasing" → AntitoneOn, MonotoneOn (weak); "strictly increasing" is StrictMonoOn; reason: the paper uses the words in the weak sense (Lemma 3.1(ii) calls ϕ′_− decreasing for ϕ(t) = t, where it is constant; Fact 2.4(i))
--   - encoding: f : ℝⁿ → (−∞, ∞]; η ∈ (0, ∞]; ϕ : [0, η) → ℝ₊; the left derivative ϕ′_− → f : EuclideanSpace ℝ (Fin n) → EReal; η : ℝ≥0∞; ϕ : ℝ → ℝ constrained only on Ieta η = {t | 0 ≤ t ∧ ofReal t < η}; ϕ′_−(t) = derivWithin ϕ (Set.Iio t) t; reason: Lean conventions; the same instances
-- source:
--   Wang–Wang, arXiv:2008.13257v5, Lemma 3.8, p.12

import Mathlib
import Definitions.Def_ExactModKL_Ieta
import Definitions.Def_ExactModKL_leftDeriv

open scoped ENNReal
open MeasureTheory

namespace ExactModKL

/-- Lemma 3.8 (Wang–Wang, arXiv:2008.13257v5 (preprint), p.12), stated for nonnegative `h`:
let `η ∈ (0, ∞]` and `h : (0, η) → ℝ₊` decreasing, define `ϕ(t) = ∫_0^t h(s) ds` for
`t ∈ (0, η)` and `ϕ(0) = 0`, and suppose `ϕ(t) < ∞` for `t ∈ (0, η)`. Then `ϕ` is concave and
increasing on `[0, η)`, right-continuous at `0`, with `ϕ′_−(t) ≥ h(t)` for `t ∈ (0, η)`; if `h` is
positive-valued, `ϕ` is strictly increasing on `[0, η)`; if in addition `h` is continuous, `ϕ` is
`C¹` on `(0, η)`.

**Formalization Note.** The paper assumes `h` positive-valued throughout; here positivity is
assumed only for the strict monotonicity, so the statement specializes to the printed lemma.
"`ϕ(t) < ∞`" is integrability of `h` on `(0, t]` (equivalent for a nonnegative monotone `h`).
`ϕ(t)` is the Lebesgue integral over `(0, t]`, which is `0` at `t = 0`. -/
theorem lemma_3_8 (η : ℝ≥0∞) (hη : 0 < η) (h : ℝ → ℝ)
    (h_nonneg : ∀ s : ℝ, 0 < s → ENNReal.ofReal s < η → 0 ≤ h s)
    (h_anti : AntitoneOn h {s | 0 < s ∧ ENNReal.ofReal s < η})
    (h_int : ∀ t : ℝ, 0 < t → ENNReal.ofReal t < η → IntegrableOn h (Set.Ioc 0 t)) :
    ConcaveOn ℝ (Ieta η) (fun t => ∫ s in Set.Ioc 0 t, h s) ∧
      MonotoneOn (fun t => ∫ s in Set.Ioc 0 t, h s) (Ieta η) ∧
      ContinuousWithinAt (fun t => ∫ s in Set.Ioc 0 t, h s) (Set.Ici 0) 0 ∧
      (∀ t : ℝ, 0 < t → ENNReal.ofReal t < η →
        h t ≤ leftDeriv (fun t => ∫ s in Set.Ioc 0 t, h s) t) ∧
      ((∀ s : ℝ, 0 < s → ENNReal.ofReal s < η → 0 < h s) →
        StrictMonoOn (fun t => ∫ s in Set.Ioc 0 t, h s) (Ieta η)) ∧
      (ContinuousOn h {s | 0 < s ∧ ENNReal.ofReal s < η} →
        ContDiffOn ℝ 1 (fun t => ∫ s in Set.Ioc 0 t, h s) {s | 0 < s ∧ ENNReal.ofReal s < η}) := by sorry

end ExactModKL
