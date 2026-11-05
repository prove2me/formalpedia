-- Prove2me | Theorems.Thm_DegenNRM_eq_12
-- name    : DegenNRM.eq_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:36:54.539733+00:00
-- url     : https://prove2.me/theorems/f9eeb66a-49ec-43d4-ada1-0c6d7d2940af
-- title:
--   (12) — the semi-fluid relaxation equals its quantile form, and the maximum is attained
-- statement:
--   Assume Assumption 1. For every capacity vector $c\ge0$ and counts $d\ge0$, the quantile program
--   $$\max_q\ \sum_{j=1}^nd_j\int_{1-q_j}^1F_j^{-1}(q)\,dq\quad\text{s.t.}\quad\sum_{j=1}^nd_ja_{j,i}q_j\le c_i\ \forall i\in[m],\quad q_j\in[0,1]\ \forall j\in[n]\tag{12}$$
--   has an optimal solution $q$, and its optimal value equals the semi-fluid value $\bar V^{\mathrm{Semi}}_c(d)$ of (9).
--
--   This turns the infinite-dimensional relaxation (9) into a finite-dimensional concave program, the form in which the semi-fluid and fluid problems are compared (Lemma 4) and in which the myopic regret is computed (16)–(19).
--
--   Differences from the source:
--
--   - encoding: m resources, n query types; query t has size ã_t ∈ A = {a_1,…,a_n} and reward r̃_t, and the type j_t is observed → resources Fin m, types Fin n; an arrival is (j, r) ∈ Fin n × ℝ with size a_j, the law of an arrival is Σ_j p_j (δ_j ⊗ F_j), and periods t ∈ [T] are the coordinates t − 1 of a path in (Fin n × ℝ)^T; reason: reading R3 of the mission (Algorithm 2 takes the type j_t as input, p.15); same instances
--   - encoding: p_j = P(ã = a_j) for the support A = {a_1,…,a_n} → p_j > 0 and Σ_j p_j = 1; reason: a support point has positive probability and κ₁ of (15) divides by p_j; this excludes only undefined cases
--   - reading: Assumption 1: F_j supported on [l_j, u_j] with density f(·|a_j) ≥ α; l_j = u_j allowed, with 'density ∞' so that any α > 0 qualifies (p.10) → α > 0 and, for every j, F_j([l_j, u_j]) = 1 and either l_j = u_j or F_j = Lebesgue·f_j with f_j(r) ≥ α on [l_j, u_j]; reason: the printed hypothesis with its point-mass convention made explicit (reading R4)
--   - reading: F_j⁻¹, the inverse distribution function (not defined in the paper) → F_j⁻¹(q) = inf{r ∈ [l_j, u_j] : F_j((−∞, r]) ≥ q}; reason: the standard generalized inverse, restricted to the reward interval (reading R5)
--   - encoding: (9): max over x_j(r) ∈ [0,1] for r ∈ [l_j, u_j] → the supremum (sSup) over measurable x_j : ℝ → [0,1]; reason: F_j lives on [l_j, u_j], so values outside do not matter; measurability makes the expectations meaningful; Lemma 3 and (12) show the supremum is attained
--   - reading: (9) and (12) for d ∈ ℝⁿ (p.13); d_j a nonnegative count (p.12) → every d ∈ ℝⁿ with d ≥ 0; reason: reading R10: (13) is (12) at d = p·s
--   - encoding: V̄^Semi_c(d) = max_q … (12) → there is an optimal q of (12) and V̄^Semi_c(d) (the supremum of (9)) equals its objective; reason: 'max' asserts attainment; both sides are then the same number
-- source:
--   Jiang, Ma & Zhang, Degeneracy is OK: Logarithmic Regret for Network Revenue Management with Indiscrete Distributions, arXiv:2210.07996v5, §3.3, (12), p.14

import Mathlib
import Definitions.Def_DegenNRM_Assumption1
import Definitions.Def_DegenNRM_semiValue
import Definitions.Def_DegenNRM_IsQuantOpt

namespace DegenNRM

/-- **(12): the quantile form of the semi-fluid relaxation** (Jiang, Ma & Zhang,
arXiv:2210.07996v5, §3.3, (12), p.14: "Following Lemma 3, V̄^Semi_c(d) in (9) can be re-written
into the following formulation").

Under Assumption 1, for every `c ≥ 0` and `d ≥ 0` the maximum of (12),
`max_q Σ_j d_j ∫_{1-q_j}^1 F_j⁻¹(q) dq` s.t. `Σ_j d_j a_{j,i} q_j ≤ c_i`, `q_j ∈ [0,1]`, is
attained, and it equals the value `V̄^Semi_c(d)` of (9).

**Formalization Note.** "max" is made explicit: there is an optimal solution `q` of (12)
(`IsQuantOpt`) and its objective equals the supremum `semiValue` of (9). -/
theorem eq_12 {m n : ℕ} (inst : Instance m n) (α : ℝ) (hA : Assumption1 inst α)
    (c : Fin m → ℝ) (hc : 0 ≤ c) (d : Fin n → ℝ) (hd : 0 ≤ d) :
    ∃ q : Fin n → ℝ, IsQuantOpt inst c d q ∧ semiValue inst c d = quantObjective inst d q := by sorry

end DegenNRM
