-- Prove2me | Theorems.Thm_DegenNRM_claim_3
-- name    : DegenNRM.claim_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:35:45.302388+00:00
-- url     : https://prove2.me/theorems/8d1fe403-a818-4206-9fe4-e65e76260401
-- title:
--   Claim 3 — $\int_{q_1}^{q_2}F_j^{-1}\le F_j^{-1}(q_1)(q_2-q_1)+(q_2-q_1)^2/\alpha$
-- statement:
--   Assume Assumption 1 with constant $\alpha$. For every type $j$ and all $q_1,q_2\in[0,1]$,
--   $$\int_{q_1}^{q_2}F_j^{-1}(q)\,dq\le F_j^{-1}(q_1)\,(q_2-q_1)+\frac{(q_2-q_1)^2}{\alpha}.$$
--   The integral is oriented, so the case $q_2<q_1$ is included, as printed.
--
--   This is the quadratic bound through which Lemmas 5–7 bound the myopic regret.
--
--   Differences from the source:
--
--   - encoding: m resources, n query types; query t has size ã_t ∈ A = {a_1,…,a_n} and reward r̃_t, and the type j_t is observed → resources Fin m, types Fin n; an arrival is (j, r) ∈ Fin n × ℝ with size a_j, the law of an arrival is Σ_j p_j (δ_j ⊗ F_j), and periods t ∈ [T] are the coordinates t − 1 of a path in (Fin n × ℝ)^T; reason: reading R3 of the mission (Algorithm 2 takes the type j_t as input, p.15); same instances
--   - encoding: p_j = P(ã = a_j) for the support A = {a_1,…,a_n} → p_j > 0 and Σ_j p_j = 1; reason: a support point has positive probability and κ₁ of (15) divides by p_j; this excludes only undefined cases
--   - reading: Assumption 1: F_j supported on [l_j, u_j] with density f(·|a_j) ≥ α; l_j = u_j allowed, with 'density ∞' so that any α > 0 qualifies (p.10) → α > 0 and, for every j, F_j([l_j, u_j]) = 1 and either l_j = u_j or F_j = Lebesgue·f_j with f_j(r) ≥ α on [l_j, u_j]; reason: the printed hypothesis with its point-mass convention made explicit (reading R4)
--   - reading: F_j⁻¹, the inverse distribution function (not defined in the paper) → F_j⁻¹(q) = inf{r ∈ [l_j, u_j] : F_j((−∞, r]) ≥ q}; reason: the standard generalized inverse, restricted to the reward interval (reading R5)
-- source:
--   Jiang, Ma & Zhang, Degeneracy is OK: Logarithmic Regret for Network Revenue Management with Indiscrete Distributions, arXiv:2210.07996v5, Claim 3, p.47; proof p.48

import Mathlib
import Definitions.Def_DegenNRM_Assumption1
import Definitions.Def_DegenNRM_quantile

namespace DegenNRM

/-- **Claim 3: a quadratic bound on integrals of the quantile function** (Jiang, Ma & Zhang,
arXiv:2210.07996v5, Claim 3, p.47).

Under Assumption 1 with density lower bound `α`, for every type `j` and all `q₁, q₂ ∈ [0, 1]`,

`∫_{q₁}^{q₂} F_j⁻¹(q) dq ≤ F_j⁻¹(q₁) · (q₂ - q₁) + (q₂ - q₁)² / α`.

**Formalization Note.** The integral is the oriented interval integral, so the case `q₂ < q₁`
is included, as printed ("for any q1, q2 ∈ [0, 1]"). -/
theorem claim_3 {m n : ℕ} (inst : Instance m n) (α : ℝ) (hA : Assumption1 inst α) (j : Fin n)
    (q₁ q₂ : ℝ) (hq₁ : q₁ ∈ Set.Icc (0 : ℝ) 1) (hq₂ : q₂ ∈ Set.Icc (0 : ℝ) 1) :
    ∫ q in q₁..q₂, quantile inst j q ≤
      quantile inst j q₁ * (q₂ - q₁) + (q₂ - q₁) ^ 2 / α := by sorry

end DegenNRM
