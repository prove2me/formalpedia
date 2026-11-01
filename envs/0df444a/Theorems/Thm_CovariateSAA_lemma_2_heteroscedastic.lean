-- Prove2me | Theorems.Thm_CovariateSAA_lemma_2_heteroscedastic
-- name    : CovariateSAA.lemma_2_heteroscedastic
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:29:01.102997+00:00
-- url     : https://prove2.me/theorems/b9595a1a-5e59-4e1e-ab1a-18bb089b4131
-- title:
--   Lemma 2, part 2 — heteroscedastic bound (10) on the mean deviation $\frac1n\sum_i\|\tilde\varepsilon^i_n(x)\|$
-- statement:
--   Let $\hat f_n$, $\hat Q_n$ be regression estimates of $f^*$, $Q^*$, fix a sample size $n$, a realization of the data $(x^i,\varepsilon^i)$, $y^i = f^*(x^i)+Q^*(x^i)\varepsilon^i$, with $Q^*(x^i)$ invertible, and a covariate value $x$. In the heteroscedastic setting the mean deviation satisfies
--   $$
--   \begin{aligned}
--   \frac1n\sum_{i=1}^n\|\tilde\varepsilon^i_n(x)\| \le{}& \|\hat f_n(x)-f^*(x)\| + \|\hat Q_n(x)-Q^*(x)\|\Bigl(\frac1n\sum_{i=1}^n\|\varepsilon^i\|\Bigr) \\
--   &+ \|\hat Q_n(x)\|\Bigl(\frac1n\sum_{i=1}^n\bigl\|[\hat Q_n(x^i)]^{-1}-[Q^*(x^i)]^{-1}\bigr\|^2\Bigr)^{1/2}\Bigl(\frac1n\sum_{i=1}^n\|Q^*(x^i)\|^4\Bigr)^{1/4}\Bigl(\frac1n\sum_{i=1}^n\|\varepsilon^i\|^4\Bigr)^{1/4} \\
--   &+ \|\hat Q_n(x)\|\Bigl(\frac1n\sum_{i=1}^n\bigl\|[\hat Q_n(x^i)]^{-1}\bigr\|^2\Bigr)^{1/2}\Bigl(\frac1n\sum_{i=1}^n\|f^*(x^i)-\hat f_n(x^i)\|^2\Bigr)^{1/2}.
--   \end{aligned}
--   $$
--   Here $\tilde\varepsilon^i_n(x) = (\hat f_n(x)+\hat Q_n(x)\hat\varepsilon^i_n)-(f^*(x)+Q^*(x)\varepsilon^i)$ with residuals $\hat\varepsilon^i_n = [\hat Q_n(x^i)]^{-1}(y^i-\hat f_n(x^i))$, and matrix norms are induced (operator) norms.
--
--   Each of the four terms is a product of a regression error and a moment of the data, so consistency of the estimates (Assumption 5) and laws of large numbers for the moments (Assumptions 3–4) make the mean deviation vanish in probability; this is the core estimate behind Proposition 4.
--
--   Differences from the source:
--   - generalization: data (yⁱ, xⁱ) drawn from the model Y = f*(X) + Q*(X)ε; εⁱ := [Q*(xⁱ)]⁻¹(yⁱ − f*(xⁱ)) → any realization xⁱ, εⁱ with yⁱ := f*(xⁱ) + Q*(xⁱ)εⁱ; reason: the inequality is deterministic and holds for every realization; the paper's realizations are instances.
--   - generalization: Q*(x̄) ≻ 0 for every x̄ in the support 𝒳 (p.5) → Q*(xⁱ) invertible for i ≤ n; reason: the proof uses only [Q*(xⁱ)]⁻¹Q*(xⁱ) = I; positive definiteness on 𝒳 and xⁱ ∈ 𝒳 imply it.
--   - generalization: Q̂_n nonsingular with [Q̂_n(x̄)]⁻¹ ≻ 0 (p.6, Lemma 2) → no assumption on Q̂_n; [·]⁻¹ is Ring.inverse (0 on singular operators); reason: the argument holds for any operator in place of [Q̂_n(xⁱ)]⁻¹; nonsingular Q̂_n are an instance.
--   - encoding: vectors in ℝ^d with the Euclidean norm, matrices Q*(x), Q̂_n(x) with the induced matrix norm, samples i ∈ [n], proj_𝒴 the orthogonal projection → EuclideanSpace ℝ (Fin d), continuous linear maps with the operator norm, i : Fin n (0-indexed), a nearest-point map onto 𝒴; reason: Lean convention; same instances.
--   - encoding: powers 1/2 and 1/4 of empirical means → Real.sqrt and the real power (·)^(1/4) of nonnegative empirical means; reason: same values on nonnegative arguments.
-- source:
--   Kannan, Bayraksan & Luedtke, Data-Driven Sample Average Approximation with Covariate Information, arXiv:2207.13554v1, Lemma 2, part 2, inequality (10), p.9

import Mathlib
import Definitions.Def_CovariateSAA_Setting

namespace CovariateSAA

/-- **Lemma 2, part 2** (Kannan, Bayraksan & Luedtke, *Data-Driven Sample Average
Approximation with Covariate Information*, arXiv:2207.13554v1, inequality (10), p.9). In the
heteroscedastic setting,
`(1/n) Σ ‖ε̃ⁱ_n(x)‖ ≤ ‖f̂_n(x) − f*(x)‖ + ‖Q̂_n(x) − Q*(x)‖ ((1/n) Σ ‖εⁱ‖)
  + ‖Q̂_n(x)‖ ((1/n) Σ ‖[Q̂_n(xⁱ)]⁻¹ − [Q*(xⁱ)]⁻¹‖²)^{1/2} ((1/n) Σ ‖Q*(xⁱ)‖⁴)^{1/4} ((1/n) Σ ‖εⁱ‖⁴)^{1/4}
  + ‖Q̂_n(x)‖ ((1/n) Σ ‖[Q̂_n(xⁱ)]⁻¹‖²)^{1/2} ((1/n) Σ ‖f*(xⁱ) − f̂_n(xⁱ)‖²)^{1/2}`.

Deterministic: for every `n`, `ω`, `x`, given that `Q*(xⁱ)` is invertible for the data used
(the paper assumes `Q*(x̄) ≻ 0` on the support of `X`).

**Formalization Note** Norms of `Q*`, `Q̂_n` and their inverses are operator norms; `[·]⁻¹` is
`Ring.inverse`. No nonsingularity of `Q̂_n` is assumed (the paper's preamble
`[Q̂_n(x̄)]⁻¹ ≻ 0`): the inequality holds for `Ring.inverse` of any operator. -/
theorem lemma_2_heteroscedastic {dx dy : ℕ} {Ω : Type*} (D : Data dx dy Ω) (x : Vec dx) (n : ℕ)
    (ω : Ω) (hQ : ∀ i : Fin n, IsUnit (D.Qstar (D.xs i ω))) :
    empMean n (fun i => ‖epsTilde D x n ω i‖) ≤
      ‖D.fhat n ω x - D.fstar x‖ +
      ‖D.Qhat n ω x - D.Qstar x‖ * empMean n (fun i => ‖D.eps i ω‖) +
      ‖D.Qhat n ω x‖ *
        Real.sqrt (empMean n (fun i =>
          ‖Ring.inverse (D.Qhat n ω (D.xs i ω)) - Ring.inverse (D.Qstar (D.xs i ω))‖ ^ 2)) *
        empMean n (fun i => ‖D.Qstar (D.xs i ω)‖ ^ 4) ^ ((1 : ℝ) / 4) *
        empMean n (fun i => ‖D.eps i ω‖ ^ 4) ^ ((1 : ℝ) / 4) +
      ‖D.Qhat n ω x‖ *
        Real.sqrt (empMean n (fun i => ‖Ring.inverse (D.Qhat n ω (D.xs i ω))‖ ^ 2)) *
        Real.sqrt (empMean n (fun i => ‖D.fstar (D.xs i ω) - D.fhat n ω (D.xs i ω)‖ ^ 2)) := by sorry

end CovariateSAA
