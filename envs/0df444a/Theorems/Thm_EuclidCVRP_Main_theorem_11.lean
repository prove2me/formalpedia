-- Prove2me | Theorems.Thm_EuclidCVRP_Main_theorem_11
-- name    : EuclidCVRP.Main.theorem_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:09:06.234312+00:00
-- url     : https://prove2.me/theorems/870039fc-38d5-4786-9320-910cd1d97ca4
-- title:
--   Theorem 11 — CVRP with many tours reduces to Unsplittable q-path
-- statement:
--   There are absolute constants $C>0$ and $\varepsilon_0>0$ such that the following holds for every $\varepsilon=1/m<\varepsilon_0$ ($m\in\mathbb N$) and every $D$. There are $\Gamma$ (the "many tours" threshold) and $\sigma_0$ (a bound on the number of terminal pairs), depending only on $\varepsilon$ and $D$, such that for every $\alpha\ge1$: if there is an $\alpha$-approximation algorithm for Unsplittable q-path with parameter $\varepsilon$, on instances with at most $\sigma_0$ pairs, with running time polynomial in $n$, $q$ and $N$, then there is a polynomial-time algorithm that on every valid $D$-bounded CVRP instance with many tours (every optimal solution has at least $\Gamma$ tours) outputs a feasible solution of cost at most
--
--   $$\alpha\,(1+C\varepsilon)\cdot c(\mathcal T')\quad\text{for every feasible solution }\mathcal T'.$$
--
--   With Theorem 12 this gives Theorem 3.
--
--   Differences from the source:
--   - reading: a polynomial-time algorithm, no machine model fixed → a Mathlib TM2ComputableInPolyTime machine over Bool with finite stack alphabets, polynomial in the input bit length, halting on every bit string; input the binary encoding of an instance with rational coordinates and Q, d(v) in binary; reason: the paper fixes no model; a Turing machine cannot read real coordinates; this is the platform's published convention (SteinerAPX_NetworkApproximation, RevRedSAT_FiniteAlphabets), and Q in binary is the point of the paper (Section 5 treats Q ≤ n^{O(1)} separately)
--   - encoding: a collection of tours, each client on exactly one tour → a list of tours (lists of client indices) in which every client occurs exactly once overall; empty tours (cost 0) are allowed; reason: empty tours change neither feasibility nor cost, so the optimum is unchanged
--   - encoding: cost at most α · opt → cost at most α times the cost of every feasible solution; reason: a feasible solution always exists (one tour per client) and the optimum is attained, so this is the same condition
--   - reading: for any fixed ε > 0, q-path with parameter ε → ε = 1/m for m ∈ ℕ; reason: the parameter of Definition 10 cuts the sides into 1/ε segments, which needs 1/ε ∈ ℕ
--   - reading: O(ε), ε sufficiently small → an absolute constant C and the claim for ε < ε₀; reason: standing convention, p. 6; C does not depend on D
--   - reading: σ = O_ε(1) pairs; "many tours" with Γ = O_ε(1) → σ₀ and Γ existential after ε, D and before α; reason: the reduction creates at most (4/ε)N_type pairs per cell and needs Γ = 2N_type K³/ε + 1 (pp. 18–19), independent of α
--   - reading: running time polynomial in n, q and N → polynomial in the length of an encoding starting with q + N in unary; reason: q and N are numbers, not bit lengths
--   - reading: an α-approximation algorithm for unsplittable q-path → the guarantee on feasible instances only; reason: an infeasible instance has no solution to approximate; feasibility can be checked (p. 13)
--   - encoding: O_ε(1)-bounded instances → D-bounded instances for every constant D; reason: same
-- source:
--   Jannis Blauth, Fabrizio Grandoni, Bence Mátravölgyi, Ramin Mousavi, Kinter Ren, Mohammad R. Salavatipour, STOC 2027 submission #1236 (October 2026), p. 13, Theorem 11 (thresholds from §§3.3–3.5, pp. 16, 18–19)

import Mathlib
import Definitions.Def_EuclidCVRP_Main_QPath

set_option autoImplicit false

namespace EuclidCVRP.Main

/-- **Theorem 11** (p. 13). For any fixed `ε = 1/m` (small enough), given an `α`-approximation algorithm
for Unsplittable q-path with parameter `ε` and running time polynomial in `n`, `q` and `N`, there is a
polynomial-time `α(1 + O(ε))`-approximation algorithm for `D`-bounded instances of CVRP with many
tours. The `O(ε)` is an absolute constant `C`; the threshold `Γ` of "many tours" and the bound `σ₀` on
the number of terminal pairs of the q-path instances used depend only on `ε` and `D`. -/
theorem theorem_11 :
    ∃ C : ℝ, 0 < C ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ m : ℕ, 0 < m → (1 / (m : ℝ)) < ε₀ → ∀ D : ℝ, ∃ Γ : ℕ, ∃ σ₀ : ℕ,
        ∀ α : ℝ, 1 ≤ α →
          (∃ qalg : List Bool → List (List (List ℕ)), IsQPathApproxAlg m σ₀ α qalg) →
          ∃ alg : List Bool → List (List ℕ),
            IsApproxAlg (α * (1 + C * (1 / (m : ℝ))))
              (fun J => J.toInstance.DBounded D ∧ J.toInstance.ManyTours Γ) alg := by sorry

end EuclidCVRP.Main
