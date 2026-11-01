-- Prove2me | Theorems.Thm_CovariateSAA_lemma_3
-- name    : CovariateSAA.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:28:58.080967+00:00
-- url     : https://prove2.me/theorems/e57e1634-a132-4781-b9a7-b552e7e47796
-- title:
--   Lemma 3 — Minkowski bound on $\bigl(\frac1n\sum_i\|[\hat Q_n(x^i)]^{-1}\|^2\bigr)^{1/2}$
-- statement:
--   For regression estimates $\hat Q_n$ of $Q^*$ and data $x^1,\dots,x^n$,
--   $$
--   \Bigl(\frac1n\sum_{i=1}^n\bigl\|[\hat Q_n(x^i)]^{-1}\bigr\|^2\Bigr)^{1/2} \le \Bigl(\frac1n\sum_{i=1}^n\bigl\|[\hat Q_n(x^i)]^{-1}-[Q^*(x^i)]^{-1}\bigr\|^2\Bigr)^{1/2} + \Bigl(\frac1n\sum_{i=1}^n\bigl\|[Q^*(x^i)]^{-1}\bigr\|^2\Bigr)^{1/2},
--   $$
--   the norms being induced matrix norms.
--
--   Combined with Assumptions 3 and (5d), the lemma shows that the factor $\bigl(\frac1n\sum_i\|[\hat Q_n(x^i)]^{-1}\|^2\bigr)^{1/2}$ in the last term of inequality (10) stays bounded in probability.
--
--   Differences from the source:
--   - generalization: Q̂_n nonsingular (p.6) and Q* positive definite (p.5) → arbitrary operators, [·]⁻¹ = Ring.inverse; reason: the inequality is the triangle inequality in ℓ² applied to the operator norms and holds for any operators; the paper's case is an instance.
--   - encoding: vectors in ℝ^d with the Euclidean norm, matrices Q*(x), Q̂_n(x) with the induced matrix norm, samples i ∈ [n], proj_𝒴 the orthogonal projection → EuclideanSpace ℝ (Fin d), continuous linear maps with the operator norm, i : Fin n (0-indexed), a nearest-point map onto 𝒴; reason: Lean convention; same instances.
-- source:
--   Kannan, Bayraksan & Luedtke, Data-Driven Sample Average Approximation with Covariate Information, arXiv:2207.13554v1, Lemma 3, p.12

import Mathlib
import Definitions.Def_CovariateSAA_Setting

namespace CovariateSAA

/-- **Lemma 3** (Kannan, Bayraksan & Luedtke, *Data-Driven Sample Average Approximation with
Covariate Information*, arXiv:2207.13554v1, p.12). We have
`((1/n) Σ ‖[Q̂_n(xⁱ)]⁻¹‖²)^{1/2} ≤ ((1/n) Σ ‖[Q̂_n(xⁱ)]⁻¹ − [Q*(xⁱ)]⁻¹‖²)^{1/2}
  + ((1/n) Σ ‖[Q*(xⁱ)]⁻¹‖²)^{1/2}`.

**Formalization Note** Operator norms; `[·]⁻¹` is `Ring.inverse`, and the inequality is stated
for all estimates and data, with no nonsingularity assumption. -/
theorem lemma_3 {dx dy : ℕ} {Ω : Type*} (D : Data dx dy Ω) (n : ℕ) (ω : Ω) :
    Real.sqrt (empMean n (fun i => ‖Ring.inverse (D.Qhat n ω (D.xs i ω))‖ ^ 2)) ≤
      Real.sqrt (empMean n (fun i =>
        ‖Ring.inverse (D.Qhat n ω (D.xs i ω)) - Ring.inverse (D.Qstar (D.xs i ω))‖ ^ 2)) +
      Real.sqrt (empMean n (fun i => ‖Ring.inverse (D.Qstar (D.xs i ω))‖ ^ 2)) := by sorry

end CovariateSAA
