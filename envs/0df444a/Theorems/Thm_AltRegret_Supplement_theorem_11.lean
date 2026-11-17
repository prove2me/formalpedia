-- Prove2me | Theorems.Thm_AltRegret_Supplement_theorem_11
-- name    : AltRegret.Supplement.theorem_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T00:13:24.396942+00:00
-- url     : https://prove2.me/theorems/5bc9b8e6-9e26-4db9-ad52-c7da5ed91d99
-- title:
--   Theorem 11 — monotonicity of the continuous potential (corrected: $0\le\eta$)
-- statement:
--   Let $X$ be a nonempty compact convex set, let $\mu$ be a Borel reference probability on $X$, and let $f_t:X\to[-1,1]$ be continuous and convex. If
--   $$
--   0\le\eta\le\frac18,
--   \qquad
--   \beta=\frac\eta4,
--   $$
--   then every round $t\ge1$ of continuous AA-Hedge satisfies
--   $$
--   \Phi_{t+1}\le\Phi_t\le0.
--   $$
--   Here $\Phi_t$ is the integral potential of equation (6).
--
--   This is the monotonicity statement used to prove Theorem 7.
--
--   Differences from the source:
--   - correction: η≤1/8 → 0≤η≤1/8; reason: if η<0 then β=η/4<0 and the quadratic exponent tends to +∞ as |θ|→∞, so the displayed maximum is unbounded; at η=0 the potential is identically zero
--   - encoding: Φ_t is defined by a maximum over θ∈ℝ → Φ_t is the real supremum of the same objective; reason: under the corrected hypotheses the objective has an attained finite maximum, so the values coincide
-- source:
--   Tao, Zheng, Optimal Alternating Regret for Online Learning and Games, arXiv:2608.24731, Theorem 11, p.20; equation (6), p.19

import Mathlib
import Definitions.Def_AltRegret_Supplement_ContinuousAAHedgeRun

open MeasureTheory

namespace AltRegret.Supplement

/-- **Theorem 11 (Monotonicity of potential), corrected.** Tao–Zheng,
*Optimal Alternating Regret for Online Learning and Games*, arXiv:2608.24731, Theorem 11,
p.20. If `0 ≤ η ≤ 1/8` and `β=η/4`, the integral potential (6) is nonincreasing and at most
zero.

**Formalization Note.** The printed theorem only says `η ≤ 1/8`. The added `0 ≤ η` is the
minimal correction: for `η<0`, `β=η/4<0` makes the quadratic exponent grow as `|θ|→∞`, so the
displayed maximum is unbounded. At `η=0`, the potential is identically zero. The real supremum
in `continuousPotential` is an attained finite maximum under these hypotheses. -/
theorem theorem_11 {d : ℕ} (X : Set (Point d)) (hXne : X.Nonempty)
    (hXcompact : IsCompact X) (hXconvex : Convex ℝ X)
    (f : ℕ → Point d → ℝ) (hf : IsOCOSequence X f)
    (μ : Measure (Point d)) [IsProbabilityMeasure μ] (hμX : μ X = 1)
    (η β : ℝ) (hη0 : 0 ≤ η) (hη : η ≤ 1 / 8) (hβ : β = η / 4)
    (run : ContinuousAAHedgeRun X μ f η β) :
    ∀ t, 1 ≤ t →
      continuousPotential μ f run.play η β (t + 1) ≤
          continuousPotential μ f run.play η β t ∧
        continuousPotential μ f run.play η β t ≤ 0 := by sorry

end AltRegret.Supplement
