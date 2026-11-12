-- Prove2me | Theorems.Thm_EuclidCVRP_Main_lemma_23
-- name    : EuclidCVRP.Main.lemma_23
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:08:14.830425+00:00
-- url     : https://prove2.me/theorems/63e3d984-aed3-458a-9f67-0e2e1e249131
-- title:
--   Lemma 23 — computing a compact ordering
-- statement:
--   Given the edge set $E$ of a valid pairing graph for a square with $m$ portals, a compact ordering of $E$ (Definition 22),
--
--   $$e_1,\dots,e_k\ \text{ with }\ \sum_{i=1}^{k-1}\log_2\bigl(2\,d(e_i,e_{i+1})\bigr)\le 24m,$$
--
--   can be computed in time $m^{O(1)}$: a polynomial-time machine reads $m$ in unary and any list enumerating $E$ and outputs such an ordering.
--
--   Compact orderings make the number of smooth flows polynomial (Lemma 25).
--
--   Differences from the source:
--   - reading: a polynomial-time algorithm, no machine model fixed → a Mathlib TM2ComputableInPolyTime machine over Bool with finite stack alphabets, polynomial in the input bit length, halting on every bit string; input the binary encoding of an instance with rational coordinates and Q, d(v) in binary; reason: the paper fixes no model; a Turing machine cannot read real coordinates; this is the platform's published convention (SteinerAPX_NetworkApproximation, RevRedSAT_FiniteAlphabets), and Q in binary is the point of the paper (Section 5 treats Q ≤ n^{O(1)} separately)
--   - reading: in time m^{O(1)} → polynomial in the length of the input, which contains m in unary; reason: the input length is between m and O(m log m) since a pairing graph has O(m) edges (Lemma 21)
--   - generalization: a square of the dissection (m = 4m′ portals, m′ even) → any number m of portals; reason: the statement is about a cyclically ordered set of m points; it specializes to m = 4m′
-- source:
--   Jannis Blauth, Fabrizio Grandoni, Bence Mátravölgyi, Ramin Mousavi, Kinter Ren, Mohammad R. Salavatipour, STOC 2027 submission #1236 (October 2026), p. 26, Lemma 23 (with Definition 22)

import Mathlib
import Definitions.Def_EuclidCVRP_Main_Machine
import Definitions.Def_EuclidCVRP_Main_Pairing

set_option autoImplicit false

namespace EuclidCVRP.Main

/-- **Lemma 23** (p. 26). Given the edge set `E` of a valid pairing graph for a square with `m` portals,
a compact ordering of `E` (Definition 22) is computable in time `m^{O(1)}`: a polynomial-time machine
reads `m` in unary and any list enumerating `E`, and outputs a compact ordering of `E`. -/
theorem lemma_23 :
    ∃ alg : List Bool → List PEdge,
      PolyTimeFn (listBits (fun e : PEdge => natBits e.1 ++ natBits e.2)) alg ∧
      ∀ (m : ℕ) (l : List PEdge), l.Nodup → IsPairingGraph m l.toFinset →
        IsCompactOrdering m l.toFinset
          (alg (unaryBits m ++ listBits (fun e : PEdge => natBits e.1 ++ natBits e.2) l)) := by sorry

end EuclidCVRP.Main
