-- Prove2me | Theorems.Thm_EmpiricalDRO_Coverage_proposition2_duality
-- name    : EmpiricalDRO.Coverage.proposition2_duality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T15:09:29.193504+00:00
-- url     : https://prove2.me/theorems/9ec750eb-ffd1-4ad9-8309-e394251ad83c
-- title:
--   Proposition 2, p. 23 — Z_n ≤ μ ≤ Z̄_n over U_n(κ/(2n)) if and only if −2 log R(μ) ≤ κ
-- statement:
--   Let $n\ge1$, $z=(z_1,\dots,z_n)\in\mathbb R^n$, $\mu\in\mathbb R$ and $\kappa\ge0$. Let $\mathcal U_n(\eta)$ be the empirical Burg ball and $-2\log R(\mu)$ the empirical-likelihood statistic of $z$. Then
--   $$
--   \min_{w\in\mathcal U_n(\kappa/(2n))}\sum_{i=1}^n w_iz_i\ \le\ \mu\ \le\ \max_{w\in\mathcal U_n(\kappa/(2n))}\sum_{i=1}^n w_iz_i
--   \quad\Longleftrightarrow\quad -2\log R(\mu)\le\kappa .
--   $$
--   With $\kappa=\chi^2_{1,1-\alpha}$, $z_i=h(x;\xi_i)$ and $\mu=Z_0(x)$ this reads: $\underline Z_n(x)\le Z_0(x)\le\overline Z_n(x)$ if and only if $-2\log R(Z_0(x))\le\chi^2_{1,1-\alpha}$.
--
--   This duality between the empirical DRO interval and the empirical likelihood confidence region is what transfers the $\chi^2_1$ limit of the empirical likelihood theorem to the coverage of the DRO bounds.
--
--   **Formalization Note.** The paper states Proposition 2 for $\kappa=\chi^2_{1,1-\alpha}$ "under the same conditions as Theorem 2"; its proof uses none of the probabilistic conditions, and p. 11 displays the same equivalence for a general $\kappa$. The statement here is that general deterministic form (every $n\ge1$, data vector $z$, value $\mu$ and $\kappa\ge0$), which contains the printed case. The minimum and maximum are the infimum `robustLower burg (κ/2) z` and the published supremum `robustMean burg (κ/2) z`, whose ball has radius $(\kappa/2)/n=\kappa/(2n)$.
-- source:
--   Lam, Recovering Best Statistical Guarantees via the Empirical DRO, arXiv:1605.09349v1, p. 23, Proposition 2; general-κ display, p. 11

import Mathlib
import Definitions.Def_EmpiricalDRO_Coverage_Setting
open MeasureTheory ProbabilityTheory Filter Topology

namespace EmpiricalDRO.Coverage

/-- Proposition 2, Lam, arXiv:1605.09349v1, p. 23 (general radius κ as displayed on p. 11): for a data
vector `z`, a value `μ` and `κ ≥ 0`,
`min_{U_n(κ/(2n))} ∑ wᵢ zᵢ ≤ μ ≤ max_{U_n(κ/(2n))} ∑ wᵢ zᵢ` if and only if `−2 log R(μ) ≤ κ`. -/
theorem proposition2_duality {n : ℕ} (hn : 0 < n) (z : Fin n → ℝ) (μ κ : ℝ) (hκ : 0 ≤ κ) :
    (robustLower burg (κ / 2) z ≤ μ ∧ μ ≤ GenEmpLik.Expansion.robustMean burg (κ / 2) z) ↔
      elStat z μ ≤ (κ : EReal) := by sorry

end EmpiricalDRO.Coverage
