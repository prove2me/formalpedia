-- Prove2me | Theorems.Thm_ActiveCtxSearch_lemma_9
-- name    : ActiveCtxSearch.lemma_9
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:41:23.053101+00:00
-- url     : https://prove2.me/theorems/db513e77-b1d0-450f-b2f6-6ddfd6bff1ef
-- title:
--   Lemma 9 — VC excess-error bound for ERM over non-homogeneous linear classifiers
-- statement:
--   There is a universal constant $C>0$ with the following property. Let $Q$ be a distribution on $\mathbb R^d\times\{\pm1\}$ whose context marginal is supported on $B_2(d)$, and let $V$ be any class of non-homogeneous linear classifiers $v(\cdot)=\langle\cdot,w\rangle-\beta$. Write $\mathrm{err}(v\mid Q)=\Pr_{(x,y)\sim Q}[y\neq\operatorname{sgn}(v(x))]$. Let $\varepsilon,\delta\in(0,1)$ and
--   $$n\ge C\varepsilon^{-2}\big(d+1+\ln(1/\delta)\big).$$
--   If $(x_i,y_i)_{i=1}^n$ are i.i.d. from $Q$ and $\hat v$ minimizes $\sum_{i=1}^n\mathbf 1\{y_i\neq\operatorname{sgn}(v(x_i))\}$ over $v\in V$ (with any tie-breaking rule), then with probability at least $1-\delta$
--   $$\mathrm{err}(\hat v\mid Q)-\inf_{v\in V}\mathrm{err}(v\mid Q)\le 2\varepsilon.$$
--
--   This is the standard VC bound for halfspaces with intercept (VC dimension $d+1$); Lemma 3 applies it in each epoch to the constrained class $\{\|w\|_2=1,|\beta|\le\beta_0\}$ and to the conditional law of the queried contexts.
--
--   Differences from the source:
--   - generalization: v* = arg min_{v∈V} err(v|Q) and the comparison err(v̂|Q) − err(v*|Q) → comparison with inf_{v∈V} err(v|Q); reason: equal to the printed form whenever a minimizer exists, and meaningful when none does
--   - generalization: V = all non-homogeneous linear classifiers, ERM over V → any subclass V of them, with the ERM over the same V; reason: V = all classifiers is the printed case; Lemma 3 uses the constrained class {‖w‖₂ = 1, |β| ≤ β₀}
--   - encoding: Q supported on B₂(d) × {0, 1}; ERM loss 1{yᵢ ≠ v(xᵢ)} → labels ±1; loss 1{yᵢ ≠ sgn(v(xᵢ))}; reason: the source's err compares y with sgn(v(x)) ∈ {±1}; {0, 1} and the bare v(xᵢ) are notational slips
--   - reading: with probability 1 − δ, v̂ = arg min → outer measure of the failure set ≤ δ, for every ERM selection; reason: the source does not fix a minimizer; an arbitrary selection need not make the event measurable
--   - encoding: ε → ε (the source's ϵ); reason: notation only
-- source:
--   Chen, Liu & Wang, Active Learning for Contextual Search with Binary Feedback, arXiv:2110.01072v2, Appendix A, Lemma 9, p.29

import Mathlib
import Definitions.Def_ActiveCtxSearch_Errors

open MeasureTheory

namespace ActiveCtxSearch

/-- **Lemma 9**, Chen, Liu & Wang, arXiv:2110.01072v2, p.29 (VC bound for non-homogeneous linear
classifiers). There is a universal constant `C > 0` such that the following holds. Let `Q` be a
distribution on `ℝᵈ × {±1}` whose context marginal is supported on `B₂(d)`, and let `V` be a class of
non-homogeneous linear classifiers `v(·) = ⟨·, w⟩ − β` (pairs `(w, β)`). Let `ε, δ ∈ (0, 1)` and
`n ≥ C ε⁻²(d + 1 + ln(1/δ))`. For `n` i.i.d. samples from `Q` and any empirical risk minimizer `v̂` over
`V` (any tie-breaking rule), with probability at least `1 − δ`,
`err(v̂|Q) − inf_{v ∈ V} err(v|Q) ≤ 2ε`.

**Formalization Note** Labels are `±1` (the source's `{0, 1}` is an encoding slip: its loss compares
`y` with `sgn(v(x))`), and the ERM's loss `1{yᵢ ≠ v(xᵢ)}` is `1{yᵢ ≠ sgn(v(xᵢ))}`. The source's
`v* = arg min_{v ∈ V} err(v|Q)` is replaced by the infimum, which equals it whenever a minimizer exists.
The class `V` may be any subclass of the source's class of all non-homogeneous linear classifiers
(the source's case is `V = univ`; Lemma 3 applies it to `{‖w‖₂ = 1, |β| ≤ β₀}`); the ERM is over the
same `V`. The probability is the outer measure of the failure set under the product law. -/
theorem lemma_9 :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (Q : Measure (E d × ℤ)) [IsProbabilityMeasure Q],
      Q {p | p.1 ∉ unitBall d ∨ (p.2 ≠ 1 ∧ p.2 ≠ -1)} = 0 →
      ∀ (V : Set (E d × ℝ)) (ε δ : ℝ), 0 < ε → ε < 1 → 0 < δ → δ < 1 →
      ∀ n : ℕ, C * ε⁻¹ ^ 2 * ((d : ℝ) + 1 + Real.log (1 / δ)) ≤ n →
      ∀ erm : (Fin n → E d × ℤ) → E d × ℝ,
        (∀ S, erm S ∈ V ∧ ∀ c ∈ V, empLoss (List.ofFn S) (erm S) ≤ empLoss (List.ofFn S) c) →
        (Measure.pi fun _ : Fin n => Q)
            {S | 2 * ε < clsErr Q (erm S) - sInf (clsErr Q '' V)} ≤ ENNReal.ofReal δ := by sorry

end ActiveCtxSearch
