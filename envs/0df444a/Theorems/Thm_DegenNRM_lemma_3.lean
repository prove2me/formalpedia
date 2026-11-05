-- Prove2me | Theorems.Thm_DegenNRM_lemma_3
-- name    : DegenNRM.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:35:35.490217+00:00
-- url     : https://prove2.me/theorems/2c994226-1171-4a4b-a832-d5daf1199ed1
-- title:
--   Lemma 3 — the semi-fluid relaxation (9) has a threshold optimal solution (corrected: fractional value at the threshold)
-- statement:
--   Assume Assumption 1. For every capacity vector $c\ge0$ and counts $d\ge0$, problem (9) has an optimal solution $x^*$ of threshold form: there are thresholds $\theta_1,\dots,\theta_n$ such that, for every type $j$ and reward $r$,
--   $$x^*_j(r)=1\ \text{ if } r>\theta_j,\qquad x^*_j(r)=0\ \text{ if } r<\theta_j.$$
--   Optimality means that $x^*$ is feasible and attains the supremum $\bar V^{\mathrm{Semi}}_c(d)$.
--
--   The threshold form is what allows (9) to be rewritten as the quantile program (12).
--
--   **Formalization Note** The thresholds are called $\theta_j$ here; the paper calls them $\kappa_j$, which are unrelated to $\kappa_1$.
--
--   Differences from the source:
--
--   - encoding: m resources, n query types; query t has size ã_t ∈ A = {a_1,…,a_n} and reward r̃_t, and the type j_t is observed → resources Fin m, types Fin n; an arrival is (j, r) ∈ Fin n × ℝ with size a_j, the law of an arrival is Σ_j p_j (δ_j ⊗ F_j), and periods t ∈ [T] are the coordinates t − 1 of a path in (Fin n × ℝ)^T; reason: reading R3 of the mission (Algorithm 2 takes the type j_t as input, p.15); same instances
--   - encoding: p_j = P(ã = a_j) for the support A = {a_1,…,a_n} → p_j > 0 and Σ_j p_j = 1; reason: a support point has positive probability and κ₁ of (15) divides by p_j; this excludes only undefined cases
--   - reading: Assumption 1: F_j supported on [l_j, u_j] with density f(·|a_j) ≥ α; l_j = u_j allowed, with 'density ∞' so that any α > 0 qualifies (p.10) → α > 0 and, for every j, F_j([l_j, u_j]) = 1 and either l_j = u_j or F_j = Lebesgue·f_j with f_j(r) ≥ α on [l_j, u_j]; reason: the printed hypothesis with its point-mass convention made explicit (reading R4)
--   - encoding: (9): max over x_j(r) ∈ [0,1] for r ∈ [l_j, u_j] → the supremum (sSup) over measurable x_j : ℝ → [0,1]; reason: F_j lives on [l_j, u_j], so values outside do not matter; measurability makes the expectations meaningful; Lemma 3 and (12) show the supremum is attained
--   - correction: x*_j(r) = 1 iff r ≥ κ_j and x*_j(r) = 0 iff r < κ_j (a {0,1}-valued solution) → x*_j(r) = 1 for r > θ_j and 0 for r < θ_j, the value at r = θ_j free in [0,1]; reason: false for point masses, which Assumption 1 allows: n = m = 1, l₁ = u₁ = 1, a₁ = 1, d = 2, c = 1 gives (9) = max 2x(1) s.t. 2x(1) ≤ 1, whose only optimum is x(1) = 1/2
--   - reading: (9) is posed for d ∈ ℝⁿ (p.13); d_j is a nonnegative count (p.12) → every d ∈ ℝⁿ with d ≥ 0; reason: reading R10: (9) is also used at d = p·s in (11)
-- source:
--   Jiang, Ma & Zhang, Degeneracy is OK: Logarithmic Regret for Network Revenue Management with Indiscrete Distributions, arXiv:2210.07996v5, Lemma 3, p.14; proof pp.40

import Mathlib
import Definitions.Def_DegenNRM_Assumption1
import Definitions.Def_DegenNRM_semiValue

open MeasureTheory

namespace DegenNRM

/-- **Lemma 3, corrected: threshold optimal solutions of (9)** (Jiang, Ma & Zhang,
arXiv:2210.07996v5, Lemma 3, p.14).

Under Assumption 1, for every capacity vector `c ≥ 0` and counts `d ≥ 0`, problem (9) has an
optimal solution `x*` of threshold form: there are thresholds `θ_j` with `x*_j(r) = 1` for
`r > θ_j` and `x*_j(r) = 0` for `r < θ_j`, for every type `j`.

**Formalization Note.** The printed lemma asks for `x*_j(r) = 1` iff `r ≥ κ_j` and `0` iff
`r < κ_j`, a `{0,1}`-valued solution. That is false when a type's reward is a point mass
(allowed by Assumption 1): with `n = m = 1`, `l₁ = u₁ = 1`, `a₁ = 1`, `d = 2`, `c = 1`, (9) is
`max 2x(1)` s.t. `2x(1) ≤ 1`, whose unique optimum is `x(1) = 1/2`. The value at the threshold
itself is therefore left free in `[0, 1]`. Optimality is `semiObjective = semiValue` (the
supremum of (9) is attained by `x*`). The thresholds are named `θ` to avoid a clash with `κ₁`. -/
theorem lemma_3 {m n : ℕ} (inst : Instance m n) (α : ℝ) (hA : Assumption1 inst α)
    (c : Fin m → ℝ) (hc : 0 ≤ c) (d : Fin n → ℝ) (hd : 0 ≤ d) :
    ∃ x : Fin n → ℝ → ℝ, SemiFeasible inst c d x ∧
      semiObjective inst d x = semiValue inst c d ∧
      ∃ θ : Fin n → ℝ, ∀ j r, (θ j < r → x j r = 1) ∧ (r < θ j → x j r = 0) := by sorry

end DegenNRM
