-- Prove2me | Theorems.Thm_DeepQOperator_lemma_23
-- name    : DeepQOperator.lemma_23
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:00:08.649196+00:00
-- url     : https://prove2.me/theorems/ef33705e-c438-42ca-ae85-a938dc77597f
-- title:
--   Lemma 23: the optimal regret of a threshold decision is $\frac{c}{4R}\,\mathbb E\,\mathrm{Var}(U\mid Y)$
-- statement:
--   Let $U$ take values in $[-R,R]$, let $Y$ be any Euclidean observation, and let $T$ be uniform on $[-R,R]$ independently of $(U,Y)$, where $R>0$. A decoder observing $(Y,T)$ chooses between two decisions whose contrast is $c(U-T)$, $c>0$: choosing $+$ costs $c(T-U)_+$ and choosing $-$ costs $c(U-T)_+$. Then the optimal average regret is exactly
--   $$\frac{c}{4R}\,\mathbb E\,\mathrm{Var}(U\mid Y):\tag{96}$$
--   every measurable decoder has average regret at least this value, some measurable decoder attains it, and a decoder that also reads an independent random seed (randomized final decision) still has average regret at least this value.
--
--   The identity converts decision regret into posterior variance; with (69) it gives Theorem 6.
--
--   **Formalization Note** $Y$ takes values in $\mathbb R^k$. $\mathbb E\mathrm{Var}(U\mid Y)=\mathbb E[(U-\mathbb E[U\mid\sigma(Y)])^2]$. The randomized decoder's seed is a standard Borel probability space, joined by the product measure.
--
--   Differences from the source:
--   - encoding: "Y any Euclidean observation" → Y : Ω → ℝ^k; reason: a Euclidean space is ℝ^k
--   - encoding: "Its optimal average regret is exactly" → every measurable decoder is ≥ the value and some measurable decoder attains it; reason: definition of an optimum
--   - encoding: "Allowing a randomized final decision does not change this Bayes value" → every jointly measurable decoder reading an independent standard Borel seed is ≥ the value; reason: randomized decoders contain deterministic ones, so the value is unchanged iff none is below it
-- source:
--   Qi, Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions, STOC 2027 submission (manuscript sha256 9f8f3285…), Appendix N.2, Lemma 23, eq. (96), p.56 (PDF p.59)

import Mathlib

open MeasureTheory

namespace DeepQOperator

/-- **Lemma 23 (Integrated binary decision loss)** (Q. Qi, *Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions*,
STOC 2027 submission (manuscript sha256 9f8f3285…), Appendix N.2, p.56, PDF p.59).

Let `U` take values in `[-R, R]`, let `Y` be any Euclidean observation, and let `T` be uniform on
`[-R, R]` independently of `(U, Y)`, where `R > 0`. A decoder observing `(Y, T)` chooses between two
decisions whose contrast is `c(U - T)`, `c > 0`. Its optimal average regret is exactly
`(c/(4R)) E Var(U | Y)` (96). Allowing a randomized final decision does not change this Bayes value.

**Formalization Note.** Decision `true` (`+`) costs `c(T - U)₊` and `false` (`-`) costs `c(U - T)₊`.
`E Var(U | Y) = E[(U - E[U | σ(Y)])²]`. "Optimal average regret is exactly" is: every measurable
decoder has average regret at least the value, and some measurable decoder attains it. A randomized
decoder reads an independent seed from a standard Borel probability space `(Ω', ν)`; independence is
the product measure. -/
theorem lemma_23 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {k : ℕ}
    (U T : Ω → ℝ) (Y : Ω → Fin k → ℝ) (R c : ℝ) (hR : 0 < R) (hc : 0 < c)
    (hU : Measurable U) (hT : Measurable T) (hY : Measurable Y)
    (hUR : ∀ ω, U ω ∈ Set.Icc (-R) R) (hTu : pdf.IsUniform T (Set.Icc (-R) R) P)
    (hind : ProbabilityTheory.IndepFun T (fun ω => (U ω, Y ω)) P) :
    (∀ dec : (Fin k → ℝ) → ℝ → Bool, Measurable (fun p : (Fin k → ℝ) × ℝ => dec p.1 p.2) →
      c / (4 * R) * ∫ ω, (U ω - (P[U | MeasurableSpace.comap Y inferInstance]) ω) ^ 2 ∂P ≤
        ∫ ω, (if dec (Y ω) (T ω) then c * max 0 (T ω - U ω) else c * max 0 (U ω - T ω)) ∂P) ∧
    (∃ dec : (Fin k → ℝ) → ℝ → Bool, Measurable (fun p : (Fin k → ℝ) × ℝ => dec p.1 p.2) ∧
      ∫ ω, (if dec (Y ω) (T ω) then c * max 0 (T ω - U ω) else c * max 0 (U ω - T ω)) ∂P =
        c / (4 * R) * ∫ ω, (U ω - (P[U | MeasurableSpace.comap Y inferInstance]) ω) ^ 2 ∂P) ∧
    (∀ (Ω' : Type) [MeasurableSpace Ω'] [StandardBorelSpace Ω'] (ν : Measure Ω')
        [IsProbabilityMeasure ν] (dec : Ω' → (Fin k → ℝ) → ℝ → Bool),
      Measurable (fun p : Ω' × (Fin k → ℝ) × ℝ => dec p.1 p.2.1 p.2.2) →
      c / (4 * R) * ∫ ω, (U ω - (P[U | MeasurableSpace.comap Y inferInstance]) ω) ^ 2 ∂P ≤
        ∫ q, (if dec q.2 (Y q.1) (T q.1) then c * max 0 (T q.1 - U q.1)
          else c * max 0 (U q.1 - T q.1)) ∂(P.prod ν)) := by sorry

end DeepQOperator
