-- Prove2me | Theorems.Thm_DynLZ77_Main_fact_4_6
-- name    : DynLZ77.Main.fact_4_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:21:36.386301+00:00
-- url     : https://prove2.me/theorems/91e30f8c-eec1-4aad-8788-8dc733e8313a
-- title:
--   Fact 4.6 — LZ77 is a minimum-size LZ-like parsing
-- statement:
--   For every string $X$, the phrases $X[a..b]$ of $\mathrm{LZ77}(X)$ form an LZ-like parsing of $X$, and every LZ-like parsing $P$ of $X$ has at least as many phrases:
--   $$|\mathrm{LZ77}(X)|\le|P|.$$
--   This is the optimality of greedy LZ77 ([KS19, Lemma 2]); it bounds $z$ by the size $z'$ of any LZ-like input.
--
--   Differences from the source: none.
-- source:
--   Boneh, Fried, Golan, Kraus, Dynamic LZ77: No Space for Improvement, STOC 2027 submission (manuscript sha256 2a15e146…), p. 18 (PDF 20), Fact 4.6

import Mathlib
import Definitions.Def_DynLZ77_Main_Strings
import Definitions.Def_DynLZ77_Main_Structure

set_option autoImplicit false

namespace DynLZ77.Main

/-- **Fact 4.6** (p. 18). The LZ77 factorization is an LZ-like parsing of minimum size: its
phrases `X[a..b]` form an LZ-like parsing of `X`, and `|LZ77(X)| ≤ |P|` for every LZ-like parsing
`P` of `X`. -/
theorem fact_4_6 {α : Type} [DecidableEq α] (X : List α) :
    IsLZLike X ((LZ77 X).map (fun ab => sub X ab.1 ab.2)) ∧
      ∀ P : List (List α), IsLZLike X P → (LZ77 X).length ≤ P.length := by sorry

end DynLZ77.Main
