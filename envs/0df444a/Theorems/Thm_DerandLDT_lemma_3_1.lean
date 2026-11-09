-- Prove2me | Theorems.Thm_DerandLDT_lemma_3_1
-- name    : DerandLDT.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T23:04:46.379195+00:00
-- url     : https://prove2.me/theorems/6c518219-e29b-4cb6-824d-bdcc63531a00
-- title:
--   Lemma 3.1 — Chernoff bound $\Pr[|X-\mu| \ge \delta\mu] \le 2e^{-\delta^2\mu/3}$
-- statement:
--   Let $X_1, \dots, X_n$ be independent random variables taking values in $\{0, 1\}$ (not necessarily identically distributed), let $X = X_1 + \dots + X_n$ and $\mu = \mathbb E[X]$. Then for every $\delta \in [0, 1]$,
--   $$
--   \Pr\big[\,|X - \mu| \ge \delta\mu\,\big] \le 2\exp\!\left(-\frac{\delta^2 \mu}{3}\right).
--   $$
--   The paper uses it for the size of the random sample of good lines and for the number of fortunate points on a line in the proof of Lemma 6.2.
--
--   **Formalization Note** The variables are measurable real functions on a probability space, mutually independent (`iIndepFun`) and almost surely $0$ or $1$; $\mu$ is the integral of their sum.
--
--   Differences from the source:
--   - encoding: independent {0,1}-valued random variables → measurable real functions on a probability space, mutually independent, almost surely in {0,1}; reason: standard measure-theoretic model; the same distributions
-- source:
--   Harsha–Kopparty–Kumar–Saptharishi–Sudan, On derandomizing the line-point low-degree test, STOC 2027 submission (manuscript sha256 d57e7d6f…80df), Lemma 3.1, p.11

import Mathlib

set_option autoImplicit false

universe u

namespace DerandLDT

open MeasureTheory ProbabilityTheory

/-- **Lemma 3.1** (Chernoff bound). Harsha, Kopparty, Kumar, Saptharishi, Sudan, *On derandomizing the line-point low-degree test*,
STOC 2027 submission manuscript (sha256 d57e7d6f…80df), Lemma 3.1, p.11: *Let `X₁, …, X_n` be independent
random variables taking values in `{0, 1}`, let `X` be their sum and `µ = E[X]`. Then
`Pr[|X − µ| ≥ δµ] ≤ 2·exp(−δ²µ/3)` for every `δ ∈ [0, 1]`.*

**Formalization Note.** The `Xᵢ` are measurable real functions on a probability space, mutually
independent (`iIndepFun`), and almost surely `0` or `1`; they need not be identically
distributed. `µ` is the expectation `∫ ∑ᵢ Xᵢ`. -/
theorem lemma_3_1 {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : Fin n → Ω → ℝ) (hXm : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hX01 : ∀ i, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    P.real {ω | δ * (∫ ω', ∑ i, X i ω' ∂P) ≤ |∑ i, X i ω - ∫ ω', ∑ i, X i ω' ∂P|} ≤
      2 * Real.exp (-(δ ^ 2 * (∫ ω', ∑ i, X i ω' ∂P) / 3)) := by sorry

end DerandLDT
