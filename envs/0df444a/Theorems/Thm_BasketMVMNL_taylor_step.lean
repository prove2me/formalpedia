-- Prove2me | Theorems.Thm_BasketMVMNL_taylor_step
-- name    : BasketMVMNL.taylor_step
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T10:31:46.625522+00:00
-- url     : https://prove2.me/theorems/db9921d3-6184-41c4-9cc6-12ca078bf8cf
-- title:
--   EC.3, Taylor step — $R(\bar x^*)\ge(1-2J\epsilon^\prime)R(x^*)$
-- statement:
--   Under MVMNL with no interaction terms and the standing assumptions of §4, for every $\epsilon'>0$ and every assortment $x$, the output $\bar x^*$ of Algorithm U1 satisfies
--   $$
--   R(\bar x^*)\ge(1-2J\epsilon')\,R(x).
--   $$
--   With $\epsilon'=\epsilon/(2J)$ this is the accuracy part of Theorem 1.
--
--   Differences from the source:
--
--   - encoding: J groups of I products indexed (i,j) from 1; bundles y with yⱼ ∈ {0,1,…,I}; x ∈ {0,1}^{JI}; utilities θᵢ,ⱼ, μ₀ with vᵢ,ⱼ = exp θᵢ,ⱼ, v₀ = exp μ₀ → groups Fin J, products Fin I (0-based); bundles Fin J → Option (Fin I) with none for yⱼ = 0; x : Fin J → Fin I → Bool; the instance stores v, v₀ (θ = log v, μ₀ = log v₀), r and ψ; reason: the same instances, assortments and bundles
--   - encoding: "There are J groups of products and each group consists of I different products" (p.6) → 1 ≤ J and 1 ≤ I in Standing; reason: excludes only the empty instance, which the paper does not consider
--   - reading: rᵢ,ⱼ, "the revenue of product i in group j" (p.7), sign not stated → 0 ≤ rᵢ,ⱼ in Standing; reason: the plain meaning of revenue; with a negative revenue Theorem 1 is false (J = 2, I = 1, v = (0.2768, 10), r = (4.1257, −0.8847), v₀ = 53.3, ϵ = 0.1: Algorithm U1 earns 0.019083 < 0.9 · 0.021315)
--   - encoding: "Without loss of generality, we assume that the products in each group are ordered in such a way that the revenues {rᵢ,ⱼ} are non-increasing in i for each j" (p.9) → Standing.r_antitone: r j is antitone in i for every j; reason: the section's standing assumption; any instance is brought to this form by relabelling the products of each group, and revenue-ordered is defined with respect to this order
--   - reading: (3)–(4) write exp{μ(y)} for every permissible y, while (1) gives y = 0 the utility μ₀ → μ(0) = μ₀ = log v₀, so the empty bundle has weight v₀; reason: the denominator v₀ + … of Lemma 1 fixes this meaning
--   - reading: Algorithm U1 (p.13), described in prose and a box, with no cost model and no tie rule → the instrumented program algU1 in the unit-cost model Work: +, −, ×, /, comparisons, ⌈·⌉₊, array reads and writes and loop dispatch are charged where they execute; no log or exp; mⱼ is found by a multiplication loop; the DP state k stands for s = (1+ϵ′)^k; a K whose V̄₁(1) is −∞ gives no candidate; the first maximizer is kept (smallest t in a cell, smallest K overall); reason: the paper fixes neither a cost model nor a tie rule; any tie rule proves the theorem, and the operation count is the paper's count of DP evaluations
--   - reading: R(x∗)/(1 + ϵ′)^{2J} = (1 − 2Jϵ′ + (2J(2J+1)/2!)(1+ξ)^{−2J−2}ϵ′²)R(x∗) ≥ (1 − 2Jϵ′)R(x∗); "So, R(x̄∗) ≥ (1 − 2Jϵ′)R(x∗)" → (1 − 2Jϵ′)R(x) ≤ R(x̄∗); reason: the Lagrange-remainder identity is a step of the proof; the claim is its conclusion
--   - generalization: ϵ′ ∈ (0, 1/(2J)) and the optimal x∗ → every ϵ′ > 0 and every assortment x; reason: for ϵ′ ≥ 1/(2J) the left side is ≤ 0 ≤ R(x̄∗); R(x) ≤ R(x∗); both specialize to the paper's statement
-- source:
--   Jasin, Lyu, Najafi, Zhang, Assortment Optimization with Multi-Item Basket Purchase under Multivariate MNL Model, SSRN 3818886, EC.3, p.ec5, "So, R(x̄∗) ≥ (1 − 2Jϵ′)R(x∗)"

import Mathlib
import Definitions.Def_BasketMVMNL_Model
import Definitions.Def_BasketMVMNL_Rounding
import Definitions.Def_BasketMVMNL_Algorithm

namespace BasketMVMNL

/-- **EC.3, p.ec5, the Taylor step**: "So, R(x̄*) ≥ (1 − 2Jϵ′) R(x*)." Jasin, Lyu, Najafi, Zhang, *Assortment Optimization with Multi-Item Basket Purchase under
Multivariate MNL Model*, SSRN 3818886.

For every `ϵ′ > 0` and every assortment `x`, the output `x̄*` of Algorithm U1 satisfies
`R(x̄*) ≥ (1 − 2Jϵ′) R(x)`. -/
theorem taylor_step {J I : ℕ} (P : Instance J I) (hP : P.Standing) (hψ : NoInteraction P)
    (ε' : ℝ) (hε' : 0 < ε') (x : Assortment J I) :
    (1 - 2 * (J : ℝ) * ε') * R P x ≤ R P (output P ε') := by sorry

end BasketMVMNL
