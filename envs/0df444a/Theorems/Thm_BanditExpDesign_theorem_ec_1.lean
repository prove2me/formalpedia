-- Prove2me | Theorems.Thm_BanditExpDesign_theorem_ec_1
-- name    : BanditExpDesign.theorem_ec_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:35:24.381601+00:00
-- url     : https://prove2.me/theorems/da8bc713-6f9b-4278-82af-9a30874b4124
-- title:
--   Theorem EC.1 — Bernstein's inequality for martingales (corrected: for each $t$, not uniformly in $t$)
-- statement:
--   Let $X_1,X_2,\dots$ be a martingale difference sequence for a filtration $(\mathcal F_t)$ with $|X_t|\le a_t$ almost surely for a non-decreasing deterministic sequence $(a_t)$. Let $M_t=\sum_{\tau=1}^tX_\tau$, and let $\bar V_1,\bar V_2,\dots$ be deterministic with
--   $$V_t:=\sum_{\tau=1}^t\mathbb E[X_\tau^2\mid\mathcal F_{\tau-1}]\le\bar V_t\ \text{ a.s.},\qquad\sqrt{\frac{\ln(2/\delta)}{(e-2)\bar V_t}}\le\frac1{a_t},$$
--   where $\delta>0$. Then for every $t\ge1$, with probability greater than $1-\delta$,
--   $$|M_t|\le2\sqrt{(e-2)\bar V_t\ln(2/\delta)}.$$
--
--   This is the form of Freedman's inequality that controls the treatment-effect martingale of EXP3EG in Theorem 7.
--
--   **Formalization Note** The sequence $(a_t)$ is the page's $(\alpha_t)$, renamed to avoid the input $\alpha$ of EXP3EG. Indices start at $1$ and $X_0$ is ignored.
--
--   Differences from the source:
--   - correction: with probability greater than 1 − δ for all t (one event) → for every t, with probability greater than 1 − δ; reason: the printed uniform claim is false: i.i.d. ±1 steps, a_t = 1, V̄_t = max(t, ln(2/δ)/(e−2)) satisfy every assumption, and by the law of the iterated logarithm the bound fails for infinitely many t almost surely
--   - generalization: conditioning on X_1, …, X_{τ−1} → any filtration to which X is adapted; reason: the natural filtration is a special case
--   - encoding: δ unconstrained → 0 < δ; reason: for δ ≤ 0 the expression ln(2/δ) is undefined; for δ ≥ 1 the claim is still stated and still true
--   - encoding: √(ln(2/δ)/((e−2)V̄_t)) ≤ 1/α_t, which presumes V̄_t, α_t > 0 → the same inequality with x/0 = 0; reason: at V̄_t = 0 or a_t = 0 the hypothesis is automatic in Lean, and then X_s = 0 a.s. for s ≤ t and the conclusion holds, so no false instance is admitted
-- source:
--   Simchi-Levi–Wang, Multi-armed Bandit Experimental Design, SSRN 4224969, Theorem EC.1, p.ec19

import Mathlib

set_option autoImplicit false
open MeasureTheory ProbabilityTheory

namespace BanditExpDesign

/-- **Theorem EC.1 (Bernstein's Inequality)**, corrected to a fixed time, Simchi-Levi–Wang,
*Multi-armed Bandit Experimental Design*, SSRN 4224969, p.ec19. Let `X_1, X_2, …` be a martingale
difference sequence with `|X_t| ≤ a_t` almost surely for a non-decreasing deterministic sequence
`a`, let `M_t = ∑_{τ ≤ t} X_τ`, and let `V̄_t` be deterministic upper bounds on
`V_t = ∑_{τ ≤ t} E[X_τ² | 𝓕_{τ-1}]` with `√(ln(2/δ)/((e-2) V̄_t)) ≤ 1/a_t`. Then for every `t`,
with probability greater than `1 - δ`, `|M_t| ≤ 2√((e-2) V̄_t ln(2/δ))`.

**Formalization Note.** The printed clause "with probability greater than `1 - δ` for all `t`" is
false uniformly in `t` (i.i.d. `±1` steps, law of the iterated logarithm), so "for every `t`" sits
outside the probability. Only `0 < δ` is assumed (for `δ ≥ 1` the claim is still true).
Indices start at `1`, as on the page; `X 0` is ignored. `𝓕` is any
filtration, containing the natural one of the page. `a` is the page's `α`. -/
theorem theorem_ec_1 {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] (𝓕 : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ) (a Vbar : ℕ → ℝ) {δ : ℝ}
    (hδ0 : 0 < δ)
    (hadapted : ∀ s, 1 ≤ s → StronglyMeasurable[𝓕 s] (X s))
    (hmds : ∀ s, 1 ≤ s → P[X s | 𝓕 (s - 1)] =ᵐ[P] 0)
    (hbound : ∀ s, 1 ≤ s → ∀ᵐ ω ∂P, |X s ω| ≤ a s)
    (hmono : ∀ s, 1 ≤ s → a s ≤ a (s + 1))
    (hVbar : ∀ t, 1 ≤ t → ∀ᵐ ω ∂P,
      ∑ s ∈ Finset.Icc 1 t, (P[fun ω' => X s ω' ^ 2 | 𝓕 (s - 1)]) ω ≤ Vbar t)
    (hcond : ∀ t, 1 ≤ t →
      Real.sqrt (Real.log (2 / δ) / ((Real.exp 1 - 2) * Vbar t)) ≤ 1 / a t)
    (t : ℕ) (ht : 1 ≤ t) :
    1 - δ < P.real {ω | |∑ s ∈ Finset.Icc 1 t, X s ω| ≤
      2 * Real.sqrt ((Real.exp 1 - 2) * Vbar t * Real.log (2 / δ))} := by sorry

end BanditExpDesign
