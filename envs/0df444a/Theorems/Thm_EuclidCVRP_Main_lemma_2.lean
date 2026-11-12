-- Prove2me | Theorems.Thm_EuclidCVRP_Main_lemma_2
-- name    : EuclidCVRP.Main.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:07:58.257757+00:00
-- url     : https://prove2.me/theorems/0b41cbd4-c7a6-43ca-8500-d66e442401c4
-- title:
--   Lemma 2 — reduction to bounded instances [ACL10]
-- statement:
--   Let $\alpha\ge1$ and $\varepsilon>0$. There is a constant $D>0$ such that, if there is a polynomial-time $\alpha$-approximation algorithm for valid $D$-bounded instances of Euclidean CVRP (every client at distance between $1$ and $D$ from the depot), then there is a polynomial-time $(\alpha+\varepsilon)$-approximation algorithm for all valid instances of Euclidean CVRP.
--
--   This is the reduction of Adamaszek, Czumaj and Lingas; Theorem 1 applies it with $\alpha=3/2+\varepsilon/2$.
--
--   Differences from the source:
--   - reading: a polynomial-time algorithm, no machine model fixed → a Mathlib TM2ComputableInPolyTime machine over Bool with finite stack alphabets, polynomial in the input bit length, halting on every bit string; input the binary encoding of an instance with rational coordinates and Q, d(v) in binary; reason: the paper fixes no model; a Turing machine cannot read real coordinates; this is the platform's published convention (SteinerAPX_NetworkApproximation, RevRedSAT_FiniteAlphabets), and Q in binary is the point of the paper (Section 5 treats Q ≤ n^{O(1)} separately)
--   - encoding: a collection of tours, each client on exactly one tour → a list of tours (lists of client indices) in which every client occurs exactly once overall; empty tours (cost 0) are allowed; reason: empty tours change neither feasibility nor cost, so the optimum is unchanged
--   - encoding: cost at most α · opt → cost at most α times the cost of every feasible solution; reason: a feasible solution always exists (one tour per client) and the optimum is attained, so this is the same condition
--   - reading: there exists an (α + ε)-approximation for general Euclidean CVRP → a polynomial-time (α + ε)-approximation algorithm; reason: polynomial time is how [ACL10] states it and how Theorem 1 uses it; the stronger reading
-- source:
--   Jannis Blauth, Fabrizio Grandoni, Bence Mátravölgyi, Ramin Mousavi, Kinter Ren, Mohammad R. Salavatipour, STOC 2027 submission #1236 (October 2026), p. 3, Lemma 2 ([ACL10])

import Mathlib
import Definitions.Def_EuclidCVRP_Main_Machine

set_option autoImplicit false

namespace EuclidCVRP.Main

/-- **Lemma 2** ([ACL10], p. 3). Let `α ≥ 1`. For every `ε > 0` there is a constant `D > 0` such that a
polynomial-time `α`-approximation for `D`-bounded instances yields a polynomial-time
`(α + ε)`-approximation for general Euclidean CVRP. -/
theorem lemma_2 (α : ℝ) (hα : 1 ≤ α) (ε : ℝ) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧
      ((∃ alg : List Bool → List (List ℕ), IsApproxAlg α (fun J => J.toInstance.DBounded D) alg) →
        ∃ alg' : List Bool → List (List ℕ), IsApproxAlg (α + ε) (fun _ => True) alg') := by sorry

end EuclidCVRP.Main
