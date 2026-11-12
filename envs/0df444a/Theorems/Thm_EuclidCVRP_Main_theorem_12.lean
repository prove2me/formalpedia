-- Prove2me | Theorems.Thm_EuclidCVRP_Main_theorem_12
-- name    : EuclidCVRP.Main.theorem_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:09:08.179716+00:00
-- url     : https://prove2.me/theorems/9aa17ff2-d6c4-419a-9f70-78e8349a4d0f
-- title:
--   Theorem 12 — PTAS for Unsplittable q-path
-- statement:
--   There are absolute constants $C>0$ and $\varepsilon_0>0$ such that for every $\varepsilon=1/m<\varepsilon_0$ ($m\in\mathbb N$) and every bound $\sigma_0$ on the number of terminal pairs, there is an algorithm for Unsplittable q-path with parameter $\varepsilon$, with running time polynomial in $n$, $q$ and $N$, that on every feasible instance with at most $\sigma_0$ pairs outputs a feasible solution of cost at most
--
--   $$(1+C\varepsilon)\cdot(\text{cost of every feasible solution}).$$
--
--   With Theorem 11 this gives Theorem 3.
--
--   Differences from the source:
--   - reading: a polynomial-time algorithm, no machine model fixed → a Mathlib TM2ComputableInPolyTime machine over Bool with finite stack alphabets, polynomial in the input bit length, halting on every bit string; input the binary encoding of an instance with rational coordinates and Q, d(v) in binary; reason: the paper fixes no model; a Turing machine cannot read real coordinates; this is the platform's published convention (SteinerAPX_NetworkApproximation, RevRedSAT_FiniteAlphabets), and Q in binary is the point of the paper (Section 5 treats Q ≤ n^{O(1)} separately)
--   - reading: for any fixed ε > 0, q-path with parameter ε → ε = 1/m for m ∈ ℕ; reason: Definition 10 needs 1/ε ∈ ℕ
--   - reading: (1 + O(ε)), ε sufficiently small → (1 + Cε) with an absolute C, for ε < ε₀; reason: standing convention, p. 6
--   - reading: σ = O_ε(1) pairs → for every bound σ₀, a machine for the instances with σ ≤ σ₀; reason: the running time (n+N)^{σ poly(1/ε)} (p. 31) is polynomial for bounded σ
--   - reading: running time polynomial in n, q and N → polynomial in the length of an encoding starting with q + N in unary; reason: q and N are numbers, not bit lengths
--   - reading: an approximation algorithm (infeasible instances not discussed) → no requirement on infeasible instances; reason: there is nothing to approximate; feasibility can be checked separately (p. 13)
--   - reading: §4 restates the problem with positive rounded demands → nonnegative rounded demands (Definition 10); reason: Definition 10 is the formal definition Theorems 11 and 12 cite; the nonnegative case contains the positive one
-- source:
--   Jannis Blauth, Fabrizio Grandoni, Bence Mátravölgyi, Ramin Mousavi, Kinter Ren, Mohammad R. Salavatipour, STOC 2027 submission #1236 (October 2026), p. 13, Theorem 12 (proved in §4, pp. 23–31)

import Mathlib
import Definitions.Def_EuclidCVRP_Main_QPath

set_option autoImplicit false

namespace EuclidCVRP.Main

/-- **Theorem 12** (p. 13). For any fixed `ε = 1/m` (small enough) there is a `(1 + O(ε))`-approximation
algorithm for Unsplittable q-path with parameter `ε` and running time polynomial in `n`, `q` and `N`
(for every bound `σ₀` on the number `σ = O_ε(1)` of terminal pairs). The `O(ε)` is an absolute
constant `C`. -/
theorem theorem_12 :
    ∃ C : ℝ, 0 < C ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ m : ℕ, 0 < m → (1 / (m : ℝ)) < ε₀ → ∀ σ₀ : ℕ,
        ∃ alg : List Bool → List (List (List ℕ)),
          IsQPathApproxAlg m σ₀ (1 + C * (1 / (m : ℝ))) alg := by sorry

end EuclidCVRP.Main
