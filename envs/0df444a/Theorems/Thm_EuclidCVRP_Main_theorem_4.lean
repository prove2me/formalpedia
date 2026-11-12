-- Prove2me | Theorems.Thm_EuclidCVRP_Main_theorem_4
-- name    : EuclidCVRP.Main.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:07:54.531119+00:00
-- url     : https://prove2.me/theorems/19f38879-bb61-4b5e-86fd-f894ceafb676
-- title:
--   Theorem 4 — (3/2 + ε)-approximation with few tours
-- statement:
--   Let $\varepsilon>0$ and let $D$ and $\Gamma$ be constants. There is a polynomial-time algorithm that, on every valid $D$-bounded instance of Euclidean CVRP with $|\mathrm{OPT}|\le\Gamma$ (some optimal solution has at most $\Gamma$ tours), outputs a feasible solution $\mathcal T$ with
--
--   $$c(\mathcal T)\le\Bigl(\tfrac32+\varepsilon\Bigr)\,c(\mathcal T')\quad\text{for every feasible solution }\mathcal T'.$$
--
--   On other instances the output is unconstrained. Together with Theorem 3 this covers all bounded instances.
--
--   Differences from the source:
--   - reading: a polynomial-time algorithm, no machine model fixed → a Mathlib TM2ComputableInPolyTime machine over Bool with finite stack alphabets, polynomial in the input bit length, halting on every bit string; input the binary encoding of an instance with rational coordinates and Q, d(v) in binary; reason: the paper fixes no model; a Turing machine cannot read real coordinates; this is the platform's published convention (SteinerAPX_NetworkApproximation, RevRedSAT_FiniteAlphabets), and Q in binary is the point of the paper (Section 5 treats Q ≤ n^{O(1)} separately)
--   - encoding: a collection of tours, each client on exactly one tour → a list of tours (lists of client indices) in which every client occurs exactly once overall; empty tours (cost 0) are allowed; reason: empty tours change neither feasibility nor cost, so the optimum is unchanged
--   - encoding: cost at most α · opt → cost at most α times the cost of every feasible solution; reason: a feasible solution always exists (one tour per client) and the optimum is attained, so this is the same condition
--   - reading: compute in time n^{O_ε(1)} → a machine polynomial in the input bit length, the polynomial depending on ε, D, Γ; reason: Q and the demands are binary and coordinates rational; reading the input already costs its bit length
--   - encoding: |OPT| ≤ Γ with OPT an optimum with the minimum number of tours → some optimal solution has at most Γ nonempty tours; reason: equivalent
-- source:
--   Jannis Blauth, Fabrizio Grandoni, Bence Mátravölgyi, Ramin Mousavi, Kinter Ren, Mohammad R. Salavatipour, STOC 2027 submission #1236 (October 2026), p. 3, Theorem 4 (proof p. 8)

import Mathlib
import Definitions.Def_EuclidCVRP_Main_Machine

set_option autoImplicit false

namespace EuclidCVRP.Main

/-- **Theorem 4** (p. 3). Let `ε > 0`, and let `D` and `Γ` be constants. A `(3/2 + ε)`-approximate
solution of every `D`-bounded instance with `|OPT| ≤ Γ` is computable in polynomial time. -/
theorem theorem_4 (ε : ℝ) (hε : 0 < ε) (D : ℝ) (Γ : ℕ) :
    ∃ alg : List Bool → List (List ℕ),
      IsApproxAlg (3 / 2 + ε) (fun J => J.toInstance.DBounded D ∧ J.toInstance.FewTours Γ) alg := by sorry

end EuclidCVRP.Main
