-- Prove2me | Theorems.Thm_EmpiricalDRO_Consistency_uniform_weight_lower_bound
-- name    : EmpiricalDRO.Consistency.uniform_weight_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:06:22.598982+00:00
-- url     : https://prove2.me/theorems/c38f3d78-455d-4e8e-8885-bda0eed66753
-- title:
--   Proof of Theorem 6, p. 34 — with w = (1/n)_i, Z̄_n(x) − Z0(x) ≥ (1/n)Σ h̃_i
-- statement:
--   Let $n\ge1$, let $z=(z_1,\dots,z_n)$ be real numbers, let $\mu\in\mathbb R$ and $\rho\ge0$. Let $\overline Z_n$ be the maximum of $\sum_i z_iw_i$ over the empirical Burg ball $\mathcal U_n(\rho/n)$ of (19). Then
--   $$
--   \frac1n\sum_{i=1}^n(z_i-\mu)\ \le\ \overline Z_n-\mu .
--   $$
--
--   The uniform weight $w=(1/n,\dots,1/n)$ has Burg divergence $0$ and so lies in every such ball; evaluating the objective there gives the bound. In the proof of Theorem 6 (with $z_i=h(x;\xi_i)$, $\mu=Z_0(x)$, $\rho=q_n/2$) it supplies the lower half of the consistency of $\overline Z_n(x)$, since the left side tends to $0$ almost surely by the strong law.
--
--   **Formalization Note** The page uses the radius $q_n/(2n)$, i.e. $\rho=q_n/2$; the statement is given for every radius $\rho\ge0$, a disclosed generalization.
-- source:
--   Lam, Recovering Best Statistical Guarantees via the Empirical DRO, arXiv:1605.09349v1, p. 34, proof of Theorem 6, the paragraph before (78)

import Mathlib
import Definitions.Def_EmpiricalDRO_Consistency_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace EmpiricalDRO.Consistency

/-- Proof of Theorem 6, Lam, arXiv:1605.09349v1, p. 34: plugging in the uniform weight
`w = (1/n, …, 1/n)`, the upper robust value over the Burg ball of radius `ρ/n` (`ρ ≥ 0`) minus
`μ` is at least `(1/n) ∑ᵢ (zᵢ − μ)`. -/
theorem uniform_weight_lower_bound {n : ℕ} (hn : 0 < n) (z : Fin n → ℝ) (μ ρ : ℝ) (hρ : 0 ≤ ρ) :
    (1 / (n : ℝ)) * ∑ i, (z i - μ) ≤ GenEmpLik.Expansion.robustMean EmpiricalDRO.Coverage.burg ρ z - μ := by sorry

end EmpiricalDRO.Consistency
