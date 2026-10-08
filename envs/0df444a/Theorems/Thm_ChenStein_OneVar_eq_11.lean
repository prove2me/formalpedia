-- Prove2me | Theorems.Thm_ChenStein_OneVar_eq_11
-- name    : ChenStein.OneVar.eq_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:31:32.837947+00:00
-- url     : https://prove2.me/theorems/5a71ab90-750f-4df4-82bf-16dbc325c37c
-- title:
--   Display (11), p. 21 — Chen–Stein expectation bound
-- statement:
--   Under the dependent-indicator setting, let $Z$ have the Poisson law of mean $\lambda$, let $|h(k)|\le1$, and set $f=S(h-Eh(Z))$. If $|\Delta f(w)|\le D$ and $|f(w)|\le F$ for every $w$, then
--
--   $$|Eh(W)-Eh(Z)|\le(b_1+b_2)D+b'_3F.$$
--
--   This isolates the estimate that converts Stein-solution bounds into a distributional approximation bound. The paper writes $\|h\|=1$; the stated unit-ball form includes it.
--
--   **Formalization Note** The index set is countable; $X_\alpha$ are measurable Bernoulli indicators, $p_\alpha>0$, $\sum p_\alpha=\lambda>0$, and $\alpha\in B_\alpha$. The error sums are extended nonnegative reals, and $D,F$ are explicit pointwise bounds rather than real suprema.
-- source:
--   Arratia, Goldstein and Gordon, Two moments suffice for Poisson approximations: the Chen-Stein method, Ann. Probab. 17 (1989), §5, p. 21, display (11); https://doi.org/10.1214/aop/1176991491

import Mathlib
import Definitions.Def_ChenStein_OneVar_Setting

namespace ChenStein.OneVar

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- Arratia--Goldstein--Gordon (1989), §5, p. 21, display (11). -/
theorem eq_11 {Ω I : Type*} [MeasurableSpace Ω] [Countable I]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : I → Ω → ℕ) (hXm : ∀ α, Measurable (X α))
    (hX01 : ∀ α ω, X α ω ≤ 1)
    (hp : ∀ α, 0 < p P X α)
    (lam : ℝ) (hlam : HasSum (p P X) lam) (hlam0 : 0 < lam)
    (B : I → Set I) (hB : ∀ α, α ∈ B α)
    (h : ℕ → ℝ) (hh : ∀ k, |h k| ≤ 1)
    (D F : ℝ)
    (hD : ∀ w, |Δ (S lam.toNNReal (fun k => h k - poissonMean lam.toNNReal h)) w| ≤ D)
    (hF : ∀ w, |S lam.toNNReal (fun k => h k - poissonMean lam.toNNReal h) w| ≤ F) :
    ENNReal.ofReal |(∫ ω, h (W X ω) ∂P) - poissonMean lam.toNNReal h| ≤
      (b1 P X B + b2 P X B) * ENNReal.ofReal D + b3' P X B * ENNReal.ofReal F := by sorry

end ChenStein.OneVar
