-- Prove2me | Theorems.Thm_EuclidCVRP_Main_theorem_3
-- name    : EuclidCVRP.Main.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:07:50.201049+00:00
-- url     : https://prove2.me/theorems/23ba2cf8-9ab7-4c33-b065-c5de9fe7cae2
-- title:
--   Theorem 3 — (1 + ε)-approximation with many tours
-- statement:
--   Let $\varepsilon>0$ and let $D$ be a constant. There is a positive integer $\Gamma$ (depending on $\varepsilon$ and $D$) and a polynomial-time algorithm that, on every valid $D$-bounded instance of Euclidean CVRP with $|\mathrm{OPT}|\ge\Gamma$ (every optimal solution has at least $\Gamma$ tours), outputs a feasible solution $\mathcal T$ with
--
--   $$c(\mathcal T)\le(1+\varepsilon)\,c(\mathcal T')\quad\text{for every feasible solution }\mathcal T'.$$
--
--   On other instances the output is unconstrained. Together with Theorem 4 this covers all bounded instances.
--
--   Differences from the source:
--   - reading: a polynomial-time algorithm, no machine model fixed → a Mathlib TM2ComputableInPolyTime machine over Bool with finite stack alphabets, polynomial in the input bit length, halting on every bit string; input the binary encoding of an instance with rational coordinates and Q, d(v) in binary; reason: the paper fixes no model; a Turing machine cannot read real coordinates; this is the platform's published convention (SteinerAPX_NetworkApproximation, RevRedSAT_FiniteAlphabets), and Q in binary is the point of the paper (Section 5 treats Q ≤ n^{O(1)} separately)
--   - encoding: a collection of tours, each client on exactly one tour → a list of tours (lists of client indices) in which every client occurs exactly once overall; empty tours (cost 0) are allowed; reason: empty tours change neither feasibility nor cost, so the optimum is unchanged
--   - encoding: cost at most α · opt → cost at most α times the cost of every feasible solution; reason: a feasible solution always exists (one tour per client) and the optimum is attained, so this is the same condition
--   - reading: compute in time n^{O_ε(1)} → a machine polynomial in the input bit length, the polynomial depending on ε and D; reason: Q and the demands are binary and coordinates rational
--   - encoding: |OPT| ≥ Γ with OPT an optimum with the minimum number of tours → every optimal solution has at least Γ nonempty tours; reason: equivalent
-- source:
--   Jannis Blauth, Fabrizio Grandoni, Bence Mátravölgyi, Ramin Mousavi, Kinter Ren, Mohammad R. Salavatipour, STOC 2027 submission #1236 (October 2026), p. 3, Theorem 3 (proof p. 13)

import Mathlib
import Definitions.Def_EuclidCVRP_Main_Machine

set_option autoImplicit false

namespace EuclidCVRP.Main

/-- **Theorem 3** (p. 3). Let `ε > 0` and `D` be constants. There is a positive integer `Γ` such that
a `(1 + ε)`-approximate solution of every `D`-bounded instance with `|OPT| ≥ Γ` is computable in
polynomial time. -/
theorem theorem_3 (ε : ℝ) (hε : 0 < ε) (D : ℝ) :
    ∃ Γ : ℕ, 0 < Γ ∧ ∃ alg : List Bool → List (List ℕ),
      IsApproxAlg (1 + ε) (fun J => J.toInstance.DBounded D ∧ J.toInstance.ManyTours Γ) alg := by sorry

end EuclidCVRP.Main
