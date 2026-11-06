-- Prove2me | Theorems.Thm_ABPOnline_lemma_C_3
-- name    : ABPOnline.lemma_C_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:54:36.328054+00:00
-- url     : https://prove2.me/theorems/519e39e1-a78f-442d-a237-29ffa606d82d
-- title:
--   Lemma C.3 — derivative bounds $-1/(h-t)\le\partial_xv\le0$ for the Föllmer feedback of a log-concave $f$
-- statement:
--   Let $f:\mathbb R\to[0,\infty)$ be log-concave and not identically zero, and set
--   $$
--   v(t,x):=\partial_x\log P_{h-t}f(x),\qquad 0\le t<h .
--   $$
--   Then $\log P_{h-t}f$ and $v(t,\cdot)$ are differentiable and
--   $$
--   -\frac{1}{h-t}\le\partial_xv(t,x)\le0
--   $$
--   for every $0\le t<h$ and $x\in\mathbb R$. If $f$ is even, then $v(t,0)=0$ and $|v(t,x)|\le|x|/(h-t)$.
--
--   This makes one Euler step of the final-block scheme nonexpansive.
--
--   Differences from the source:
--   - encoding: f : ℝ → [0, ∞) log-concave → ConvexOptimization.LogConcaveOn univ f (f ≥ 0 and f(θx + (1 − θ)y) ≥ f(x)^θ f(y)^{1−θ}); reason: the standard definition allowing zeros
--   - reading: "for every t < h" → for every 0 ≤ t < h; reason: v is defined for 0 ≤ t < h in the same lemma
--   - encoding: ∂ₓ v(t, x) and v as derivatives → Lean's deriv, with differentiability of log P_{h−t}f and of v(t, ·) stated in the conclusion; reason: so that the bounds are not met by the junk value 0 of deriv
-- source:
--   Jo, Lee, The Exact Online Threshold for the Asymmetric Binary Perceptron, arXiv:2609.02124 (artifact sha256 bd5e2bdb18a47b7e806191ae9b888a6e4e7e150a9bd50e541b7587007d07a7a2), Lemma C.3, (98), p.40 (PDF p.41)

import Mathlib
import Definitions.Def_LogConcaveOn
import Definitions.Def_ABPOnline_heatSG

set_option autoImplicit false

namespace ABPOnline

/-- **Lemma C.3** (arXiv:2609.02124, printed p.40, PDF p.41). Let `f : ℝ → [0,∞)` be log-concave and
not identically zero, and set `v(t, x) := ∂ₓ log P_{h−t} f(x)`, `0 ≤ t < h`. Then
`−1/(h − t) ≤ ∂ₓ v(t, x) ≤ 0` for every `t < h` and `x ∈ ℝ`. If `f` is even, then `v(t, 0) = 0` and
`|v(t, x)| ≤ |x|/(h − t)`.

**Formalization Note** Log-concavity is `ConvexOptimization.LogConcaveOn univ f` (`f ≥ 0` and
`f(θx + (1−θ)y) ≥ f(x)^θ f(y)^{1−θ}`). Differentiability of `log P_{h−t} f` and of `v(t,·)` is part
of the conclusion, so the bounds are not met by Lean's junk value of `deriv`. -/
theorem lemma_C_3 (f : ℝ → ℝ) (hf : ConvexOptimization.LogConcaveOn Set.univ f)
    (hf0 : ∃ x, f x ≠ 0) (h : ℝ) :
    (∀ t x : ℝ, 0 ≤ t → t < h →
      DifferentiableAt ℝ (fun y => Real.log (heatSG (h - t) f y)) x ∧
      DifferentiableAt ℝ (fun y => follmerV h f t y) x ∧
      -1 / (h - t) ≤ deriv (fun y => follmerV h f t y) x ∧
      deriv (fun y => follmerV h f t y) x ≤ 0) ∧
    ((∀ x, f (-x) = f x) → ∀ t x : ℝ, 0 ≤ t → t < h →
      follmerV h f t 0 = 0 ∧ |follmerV h f t x| ≤ |x| / (h - t)) := by sorry

end ABPOnline
