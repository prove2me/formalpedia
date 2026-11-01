-- Prove2me | Theorems.Thm_BasketMVMNL_running_time_JM
-- name    : BasketMVMNL.running_time_JM
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T10:32:01.654985+00:00
-- url     : https://prove2.me/theorems/941ac093-f28c-4e80-ab01-e229879df544
-- title:
--   EC.3 — the running time of Algorithm U1 is $O(J^3M^2I)$
-- statement:
--   There is a universal constant $C_1$ such that for all $J,I\ge1$, every MVMNL instance with no interaction terms satisfying the standing assumptions of §4, and every $\epsilon'>0$, Algorithm U1 executes at most
--   $$
--   C_1\cdot J^3\cdot M^2\cdot I
--   $$
--   unit operations, where $M=\max_j\lceil\log_{1+\epsilon'}(1+\sum_i v_{i,j})\rceil$. The count is: $O(JM)$ values of $K$, each a DP with $J$ stages, $O(JM)$ states per stage and $O(I)$ revenue-ordered local assortments per state.
--
--   Differences from the source:
--
--   - encoding: J groups of I products indexed (i,j) from 1; bundles y with yⱼ ∈ {0,1,…,I}; x ∈ {0,1}^{JI}; utilities θᵢ,ⱼ, μ₀ with vᵢ,ⱼ = exp θᵢ,ⱼ, v₀ = exp μ₀ → groups Fin J, products Fin I (0-based); bundles Fin J → Option (Fin I) with none for yⱼ = 0; x : Fin J → Fin I → Bool; the instance stores v, v₀ (θ = log v, μ₀ = log v₀), r and ψ; reason: the same instances, assortments and bundles
--   - encoding: "There are J groups of products and each group consists of I different products" (p.6) → 1 ≤ J and 1 ≤ I in Standing; reason: excludes only the empty instance, which the paper does not consider
--   - reading: rᵢ,ⱼ, "the revenue of product i in group j" (p.7), sign not stated → 0 ≤ rᵢ,ⱼ in Standing; reason: the plain meaning of revenue; with a negative revenue Theorem 1 is false (J = 2, I = 1, v = (0.2768, 10), r = (4.1257, −0.8847), v₀ = 53.3, ϵ = 0.1: Algorithm U1 earns 0.019083 < 0.9 · 0.021315)
--   - encoding: "Without loss of generality, we assume that the products in each group are ordered in such a way that the revenues {rᵢ,ⱼ} are non-increasing in i for each j" (p.9) → Standing.r_antitone: r j is antitone in i for every j; reason: the section's standing assumption; any instance is brought to this form by relabelling the products of each group, and revenue-ordered is defined with respect to this order
--   - reading: Algorithm U1 (p.13), described in prose and a box, with no cost model and no tie rule → the instrumented program algU1 in the unit-cost model Work: +, −, ×, /, comparisons, ⌈·⌉₊, array reads and writes and loop dispatch are charged where they execute; no log or exp; mⱼ is found by a multiplication loop; the DP state k stands for s = (1+ϵ′)^k; a K whose V̄₁(1) is −∞ gives no candidate; the first maximizer is kept (smallest t in a cell, smallest K overall); reason: the paper fixes neither a cost model nor a tie rule; any tie rule proves the theorem, and the operation count is the paper's count of DP evaluations
--   - encoding: (1+ϵ′)^{mⱼ−1} < γⱼ(xⱼ) ≤ (1+ϵ′)^{mⱼ}, mⱼ = 1 if xⱼ = 0; M = maxⱼ ⌈log_{1+ϵ′}(1 + Σᵢ vᵢ,ⱼ)⌉ → mexp ϵ′ γ = least m ≥ 1 with γ ≤ (1+ϵ′)^m; γ̄ = (1+ϵ′)^{mexp}; Mcap = maxⱼ mexp(1 + Σᵢ vᵢ,ⱼ); reason: the same integers for ϵ′ > 0, γ ≥ 1 and 1 + Σᵢ vᵢ,ⱼ > 1
--   - encoding: O(J³M²I) → ≤ C₁·J³·M²·I with C₁ quantified before J, I, the instance and ϵ′; reason: the standard meaning of O(·) as a bound with one universal constant
-- source:
--   Jasin, Lyu, Najafi, Zhang, Assortment Optimization with Multi-Item Basket Purchase under Multivariate MNL Model, SSRN 3818886, EC.3, pp.ec5–ec6, "the running time complexity of Algorithm U1 is O(JM · J · JM · I) = O(J³M²I)"

import Mathlib
import Definitions.Def_BasketMVMNL_Model
import Definitions.Def_BasketMVMNL_Rounding
import Definitions.Def_BasketMVMNL_Algorithm

namespace BasketMVMNL

/-- **EC.3, pp.ec5–ec6, the running time in `M`**: "the running time complexity of Algorithm U1 is
O(JM · J · JM · I) = O(J³M²I)". Jasin, Lyu, Najafi, Zhang, *Assortment Optimization with Multi-Item Basket Purchase under
Multivariate MNL Model*, SSRN 3818886.

There is a universal constant `C₁` such that for all `J, I ≥ 1`, every no-interaction instance and
every `ϵ′ > 0`, Algorithm U1 executes at most `C₁ · J³ · M² · I` unit operations, where
`M = maxⱼ ⌈log_{1+ϵ′}(1 + Σᵢ vᵢ,ⱼ)⌉`. -/
theorem running_time_JM :
    ∃ C₁ : ℝ, ∀ {J I : ℕ} (P : Instance J I), P.Standing → NoInteraction P →
      ∀ ε' : ℝ, 0 < ε' →
        (ops P ε' : ℝ) ≤ C₁ * (J : ℝ) ^ 3 * (Mcap ε' P : ℝ) ^ 2 * (I : ℝ) := by sorry

end BasketMVMNL
