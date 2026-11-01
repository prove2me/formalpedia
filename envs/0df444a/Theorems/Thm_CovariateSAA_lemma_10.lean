-- Prove2me | Theorems.Thm_CovariateSAA_lemma_10
-- name    : CovariateSAA.lemma_10
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:28:18.791002+00:00
-- url     : https://prove2.me/theorems/d61f362b-8b4d-49a1-b519-160cfbb55c3e
-- title:
--   Lemma 10 — a uniform optimality gap away from the minimizers of a l.s.c. function on a compact set
-- statement:
--   Let $W\subset\mathbb R^{d_w}$ be nonempty and compact, let $h:W\to\mathbb R$ be lower semicontinuous, and let $W^* := \operatorname*{arg\,min}_{w\in W}h(w)$. For every $\delta>0$ there is $\kappa>0$ such that every $w\in W$ with $\operatorname{dist}(w,W^*)\ge\delta$ satisfies
--   $$
--   h(w) \ge \min_{w'\in W}h(w') + \kappa .
--   $$
--   In particular, for any $\bar w\in W$ with $\operatorname{dist}(\bar w,W^*)\ge\delta$ there is $\kappa>0$ with $h(\bar w)\ge\min_{w\in W}h(w)+\kappa$, which is the lemma as printed.
--
--   The lemma converts distance from the solution set into a gap in objective value; the proof of Theorem 5 applies it to $h=g(\cdot;x)$ on $W=\mathcal Z$ to show that ER-SAA solutions approach $S^*(x)$.
--
--   Differences from the source:
--   - generalization: for one point w̄ ∈ W with dist(w̄, W*) ≥ δ there is κ > 0 with h(w̄) ≥ min_W h + κ → for every δ > 0 there is κ > 0 with h(w) ≥ min_W h + κ for every w ∈ W with dist(w, W*) ≥ δ; reason: κ depends only on δ, as in the proof (κ = min_{W_δ} h − min_W h) and as used in (14) of the proof of Theorem 5; it implies the printed statement.
--   - encoding: h : W → ℝ lower semicontinuous, W ⊂ ℝ^{d_w} → h : ℝ^{d_w} → ℝ lower semicontinuous on W; EuclideanSpace ℝ (Fin d_w); dist = Metric.infDist; reason: only the values of h on W enter; same instances.
-- source:
--   Kannan, Bayraksan & Luedtke, Data-Driven Sample Average Approximation with Covariate Information, arXiv:2207.13554v1, Lemma 10, p.28 (Appendix A.2)

import Mathlib
import Definitions.Def_CovariateSAA_Optim

namespace CovariateSAA

/-- **Lemma 10** (Kannan, Bayraksan & Luedtke, *Data-Driven Sample Average Approximation with
Covariate Information*, arXiv:2207.13554v1, p.28), in the uniform form its proof gives. Let
`W ⊂ ℝ^{d_w}` be nonempty and compact and `h` lower semicontinuous on `W`, and let
`W* := arg min_{w ∈ W} h(w)`. Then for every `δ > 0` there is `κ > 0` such that every `w ∈ W`
with `dist(w, W*) ≥ δ` satisfies `h(w) ≥ min_{w ∈ W} h(w) + κ`.

The printed lemma fixes one point `w̄` with `dist(w̄, W*) ≥ δ` before choosing `κ`; here `κ`
depends only on `δ` (the proof's `κ = min_{W_δ} h − min_W h`), which implies the printed form.

**Formalization Note** `h` is a function on `ℝ^{d_w}` that is lower semicontinuous on `W`
(only its values on `W` enter); `dist(w, W*)` is `Metric.infDist`. -/
theorem lemma_10 {dw : ℕ} (W : Set (EuclideanSpace ℝ (Fin dw))) (hWc : IsCompact W)
    (hWne : W.Nonempty) (h : EuclideanSpace ℝ (Fin dw) → ℝ) (hh : LowerSemicontinuousOn h W) :
    ∀ δ : ℝ, 0 < δ → ∃ κ : ℝ, 0 < κ ∧ ∀ w ∈ W,
      δ ≤ Metric.infDist w (argminSet h W) → minVal h W + κ ≤ h w := by sorry

end CovariateSAA
