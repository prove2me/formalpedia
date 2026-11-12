-- Prove2me | Theorems.Thm_EuclidCVRP_Main_lemma_21
-- name    : EuclidCVRP.Main.lemma_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:07:49.421221+00:00
-- url     : https://prove2.me/theorems/62e11840-7522-4995-8386-99904c14ecbc
-- title:
--   Lemma 21 — number of pairing graphs
-- statement:
--   There is an absolute constant $C$ such that for every dissection square with $m$ portals:
--
--   1. the number of pairing graphs (sets of pairwise non-crossing edges of $H[S]$, loops included) is at most $2^{Cm}$;
--   2. every pairing graph has at most $Cm$ edges.
--
--   With $m=O(\tfrac1\varepsilon\log n)$ portals per square, the first bound is $n^{O(1/\varepsilon)}$. The lemma bounds the number of dynamic-programming configurations in the q-path PTAS.
--
--   Differences from the source:
--   - generalization: for each dissection square (m = O((1/ε) log n) portals): 2^{O(m)} = n^{O(1/ε)} → for every number m of portals: at most 2^{Cm} pairing graphs; reason: pure combinatorics of non-crossing edge sets on m cyclically ordered portals; with m ≤ C₀ log₂ n/ε it gives n^{C C₀/ε}
--   - encoding: portals numbered 1, …, m clockwise → 0, …, m−1; reason: relabelling
-- source:
--   Jannis Blauth, Fabrizio Grandoni, Bence Mátravölgyi, Ramin Mousavi, Kinter Ren, Mohammad R. Salavatipour, STOC 2027 submission #1236 (October 2026), p. 26, Lemma 21

import Mathlib
import Definitions.Def_EuclidCVRP_Main_Pairing

set_option autoImplicit false

namespace EuclidCVRP.Main

open Classical in
/-- **Lemma 21** (p. 26). For a dissection square with `m` portals, the number of pairing graphs is
`2^{O(m)}` and each pairing graph has `O(m)` edges; both `O`s are one absolute constant `C`. -/
theorem lemma_21 :
    ∃ C : ℕ, ∀ m : ℕ,
      ((Finset.range m ×ˢ Finset.range m).powerset.filter (fun E => IsPairingGraph m E)).card ≤
          2 ^ (C * m) ∧
        ∀ E : Finset PEdge, IsPairingGraph m E → E.card ≤ C * m := by sorry

end EuclidCVRP.Main
