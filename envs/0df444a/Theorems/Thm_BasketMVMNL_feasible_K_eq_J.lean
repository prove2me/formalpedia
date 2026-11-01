-- Prove2me | Theorems.Thm_BasketMVMNL_feasible_K_eq_J
-- name    : BasketMVMNL.feasible_K_eq_J
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T10:31:47.052849+00:00
-- url     : https://prove2.me/theorems/1b7bec50-4d0d-4b7c-94fa-f0eba54ef1c0
-- title:
--   EC.3 — for $K=J$ the assortment $x=0$ is feasible
-- statement:
--   Under MVMNL with no interaction terms and the standing assumptions of §4, for every $\epsilon'>0$, the dynamic program of Algorithm U1 for $K=J$, run on the group tables the algorithm computes and with the factor $\frac{v_0-1}{(1+\epsilon')^J}+1$, has a finite value:
--   $$
--   \bar V_1(1)\neq-\infty .
--   $$
--   The empty assortment $x=0$ has $\bar\gamma_j=1+\epsilon'$ in every group, so $\bar\Gamma(0)=(1+\epsilon')^J$ and the path through it reaches the terminal state $K=J$. Hence Algorithm U1 always has at least one candidate and returns a feasible output.
--
--   Differences from the source:
--
--   - encoding: J groups of I products indexed (i,j) from 1; bundles y with yⱼ ∈ {0,1,…,I}; x ∈ {0,1}^{JI}; utilities θᵢ,ⱼ, μ₀ with vᵢ,ⱼ = exp θᵢ,ⱼ, v₀ = exp μ₀ → groups Fin J, products Fin I (0-based); bundles Fin J → Option (Fin I) with none for yⱼ = 0; x : Fin J → Fin I → Bool; the instance stores v, v₀ (θ = log v, μ₀ = log v₀), r and ψ; reason: the same instances, assortments and bundles
--   - encoding: "There are J groups of products and each group consists of I different products" (p.6) → 1 ≤ J and 1 ≤ I in Standing; reason: excludes only the empty instance, which the paper does not consider
--   - reading: rᵢ,ⱼ, "the revenue of product i in group j" (p.7), sign not stated → 0 ≤ rᵢ,ⱼ in Standing; reason: the plain meaning of revenue; with a negative revenue Theorem 1 is false (J = 2, I = 1, v = (0.2768, 10), r = (4.1257, −0.8847), v₀ = 53.3, ϵ = 0.1: Algorithm U1 earns 0.019083 < 0.9 · 0.021315)
--   - encoding: "Without loss of generality, we assume that the products in each group are ordered in such a way that the revenues {rᵢ,ⱼ} are non-increasing in i for each j" (p.9) → Standing.r_antitone: r j is antitone in i for every j; reason: the section's standing assumption; any instance is brought to this form by relabelling the products of each group, and revenue-ordered is defined with respect to this order
--   - reading: Algorithm U1 (p.13), described in prose and a box, with no cost model and no tie rule → the instrumented program algU1 in the unit-cost model Work: +, −, ×, /, comparisons, ⌈·⌉₊, array reads and writes and loop dispatch are charged where they execute; no log or exp; mⱼ is found by a multiplication loop; the DP state k stands for s = (1+ϵ′)^k; a K whose V̄₁(1) is −∞ gives no candidate; the first maximizer is kept (smallest t in a cell, smallest K overall); reason: the paper fixes neither a cost model nor a tie rule; any tie rule proves the theorem, and the operation count is the paper's count of DP evaluations
--   - reading: "(xᵢ,ⱼ)ᵢ,ⱼ = 0 is a feasible solution of Algorithm U1 [for K = J]. Therefore … there exists a feasible output x̄∗" → the program's DP for K = J (dpForK on the computed tables, c = (v₀ − 1)/(1+ϵ′)^J + 1) returns V̄₁(1) ≠ ⊥; reason: feasibility of a DP is a finite optimal value; the value does not depend on c
-- source:
--   Jasin, Lyu, Najafi, Zhang, Assortment Optimization with Multi-Item Basket Purchase under Multivariate MNL Model, SSRN 3818886, EC.3, p.ec5, "When K = J, (xᵢ,ⱼ)ᵢ,ⱼ = 0 is a feasible solution of Algorithm U1"

import Mathlib
import Definitions.Def_BasketMVMNL_Model
import Definitions.Def_BasketMVMNL_Rounding
import Definitions.Def_BasketMVMNL_Algorithm

namespace BasketMVMNL

/-- **EC.3, p.ec5**: "When K = J, (xᵢ,ⱼ)ᵢ,ⱼ = 0 is a feasible solution of Algorithm U1.
Therefore, when Algorithm U1 terminates, there exists a feasible output x̄*." Jasin, Lyu, Najafi, Zhang, *Assortment Optimization with Multi-Item Basket Purchase under
Multivariate MNL Model*, SSRN 3818886.

For every `ϵ′ > 0`, the DP of Algorithm U1 for `K = J` (run on the group tables the algorithm
computes, with `c = (v₀ − 1)/(1 + ϵ′)^J + 1`) has a finite value `V̄₁(1) ≠ −∞`. -/
theorem feasible_K_eq_J {J I : ℕ} (P : Instance J I) (hP : P.Standing) (hψ : NoInteraction P)
    (ε' : ℝ) (hε' : 0 < ε') :
    ((dpForK J ((groupTables P ε').run 0).1 ((P.v0 - 1) / (1 + ε') ^ J + 1) J).run 0).1.1 ≠ ⊥ := by sorry

end BasketMVMNL
