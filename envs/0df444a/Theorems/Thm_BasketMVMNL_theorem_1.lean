-- Prove2me | Theorems.Thm_BasketMVMNL_theorem_1
-- name    : BasketMVMNL.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T10:32:06.685075+00:00
-- url     : https://prove2.me/theorems/de16f27b-7101-4690-ba1e-6c9fd27ce548
-- title:
--   Theorem 1 — Algorithm U1 is an FPTAS (corrected: $1+\log\beta$ for $\log\beta$)
-- statement:
--   There is a universal constant $C$ with the following property. Consider an MVMNL model with no interaction terms, with $J,I\ge1$, $v_{i,j}>0$, $v_0>1$, $r_{i,j}\ge0$ and revenues non-increasing in $i$ within each group. Let $\epsilon\in(0,1)$ and run Algorithm U1 with $\epsilon'=\epsilon/(2J)$. Then:
--
--   1. the returned assortment $\bar x^*$ is $(1-\epsilon)$-optimal: $R(\bar x^*)\ge(1-\epsilon)\,R(x)$ for every assortment $x\in\{0,1\}^{JI}$;
--   2. the algorithm executes at most
--   $$
--   C\cdot\frac{J^5\,I\,(1+\log\beta)^2}{\epsilon^2}
--   $$
--   unit operations, where $\beta=\max_j(1+\sum_i v_{i,j})$.
--
--   Since $\log\beta$ is linear in the input size, the algorithm is a fully polynomial-time approximation scheme for the NP-hard problem (6).
--
--   Differences from the source:
--
--   - encoding: J groups of I products indexed (i,j) from 1; bundles y with yⱼ ∈ {0,1,…,I}; x ∈ {0,1}^{JI}; utilities θᵢ,ⱼ, μ₀ with vᵢ,ⱼ = exp θᵢ,ⱼ, v₀ = exp μ₀ → groups Fin J, products Fin I (0-based); bundles Fin J → Option (Fin I) with none for yⱼ = 0; x : Fin J → Fin I → Bool; the instance stores v, v₀ (θ = log v, μ₀ = log v₀), r and ψ; reason: the same instances, assortments and bundles
--   - encoding: "There are J groups of products and each group consists of I different products" (p.6) → 1 ≤ J and 1 ≤ I in Standing; reason: excludes only the empty instance, which the paper does not consider
--   - reading: rᵢ,ⱼ, "the revenue of product i in group j" (p.7), sign not stated → 0 ≤ rᵢ,ⱼ in Standing; reason: the plain meaning of revenue; with a negative revenue Theorem 1 is false (J = 2, I = 1, v = (0.2768, 10), r = (4.1257, −0.8847), v₀ = 53.3, ϵ = 0.1: Algorithm U1 earns 0.019083 < 0.9 · 0.021315)
--   - encoding: "Without loss of generality, we assume that the products in each group are ordered in such a way that the revenues {rᵢ,ⱼ} are non-increasing in i for each j" (p.9) → Standing.r_antitone: r j is antitone in i for every j; reason: the section's standing assumption; any instance is brought to this form by relabelling the products of each group, and revenue-ordered is defined with respect to this order
--   - reading: (3)–(4) write exp{μ(y)} for every permissible y, while (1) gives y = 0 the utility μ₀ → μ(0) = μ₀ = log v₀, so the empty bundle has weight v₀; reason: the denominator v₀ + … of Lemma 1 fixes this meaning
--   - reading: Algorithm U1 (p.13), described in prose and a box, with no cost model and no tie rule → the instrumented program algU1 in the unit-cost model Work: +, −, ×, /, comparisons, ⌈·⌉₊, array reads and writes and loop dispatch are charged where they execute; no log or exp; mⱼ is found by a multiplication loop; the DP state k stands for s = (1+ϵ′)^k; a K whose V̄₁(1) is −∞ gives no candidate; the first maximizer is kept (smallest t in a cell, smallest K overall); reason: the paper fixes neither a cost model nor a tie rule; any tie rule proves the theorem, and the operation count is the paper's count of DP evaluations
--   - correction: running time O(J⁵I log²β/ϵ²) → ≤ C·J⁵·I·(1 + log β)²/ϵ²; reason: as a bound with a universal constant the printed one is false when β is close to 1: J = I = 1, v₁,₁ = δ, v₀ = 2, r₁,₁ = 1, ϵ = 1/2: the algorithm executes at least one operation while C·log²(1+δ)/ϵ² → 0 as δ → 0; for β ≥ e the corrected bound is the printed one up to a factor 4
--   - reading: "yields a (1 − ϵ)-optimal assortment" → (1 − ϵ)·R(x) ≤ R(x̄∗) for every assortment x; reason: EC.3, p.ec6: "R(x̄)∗ ≥ (1 − ϵ)R(x∗)" with x∗ optimal for (6); against every x it is equivalent
--   - encoding: O(J⁵I log²β/ϵ²) → ≤ C·J⁵·I·(1 + log β)²/ϵ² with C quantified before J, I, the instance and ϵ; reason: the standard meaning of O(·) as a bound with one universal constant
-- source:
--   Jasin, Lyu, Najafi, Zhang, Assortment Optimization with Multi-Item Basket Purchase under Multivariate MNL Model, SSRN 3818886, Theorem 1, p.14 (proof EC.3, pp.ec5–ec6)

import Mathlib
import Definitions.Def_BasketMVMNL_Model
import Definitions.Def_BasketMVMNL_Rounding
import Definitions.Def_BasketMVMNL_Algorithm

namespace BasketMVMNL

/-- **Theorem 1**, p.14 (corrected: `1 + log β` for `log β`). Jasin, Lyu, Najafi, Zhang, *Assortment Optimization with Multi-Item Basket Purchase under
Multivariate MNL Model*, SSRN 3818886.

"Suppose that we consider an MVMNL model with no interaction terms. Let ϵ ∈ (0,1). Then, setting
ϵ′ = ϵ/(2J) in Algorithm U1 yields a (1 − ϵ)-optimal assortment. Moreover, its running time is
O(J⁵ I log² β/ϵ²) where β := maxⱼ(1 + Σᵢ vᵢ,ⱼ)."

There is a universal constant `C` such that for all `J, I ≥ 1`, every no-interaction MVMNL instance
satisfying the standing assumptions of §4 and every `ϵ ∈ (0,1)`, Algorithm U1 run with
`ϵ′ = ϵ/(2J)` returns `x̄*` with `R(x̄*) ≥ (1 − ϵ) R(x)` for every assortment `x`, and executes at
most `C · J⁵ · I · (1 + log β)²/ϵ²` unit operations.

**Formalization Note.** The printed `log² β` is replaced by `(1 + log β)²`: as `β → 1` the printed
bound tends to `0` while the algorithm always executes at least one operation. For `β ≥ e` the two
agree up to a factor `4`. -/
theorem theorem_1 :
    ∃ C : ℝ, ∀ {J I : ℕ} (P : Instance J I), P.Standing → NoInteraction P →
      ∀ ε : ℝ, 0 < ε → ε < 1 →
        (∀ x : Assortment J I, (1 - ε) * R P x ≤ R P (output P (ε / (2 * (J : ℝ))))) ∧
        (ops P (ε / (2 * (J : ℝ))) : ℝ) ≤
          C * (J : ℝ) ^ 5 * (I : ℝ) * (1 + Real.log (β P)) ^ 2 / ε ^ 2 := by sorry

end BasketMVMNL
