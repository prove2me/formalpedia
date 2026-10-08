-- Prove2me | Theorems.Thm_BergeMatching_Core_lemma_5
-- name    : BergeMatching.Core.lemma_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T19:07:14.847828+00:00
-- url     : https://prove2.me/theorems/bfcdcede-d83a-48c2-ab3c-2715464346cd
-- title:
--   Lemma 5 — at most one neutral point forces a maximum matching
-- statement:
--   Let $G = (X, U)$ be a finite simple graph with a matching $V_0$, and let $N$ be the set of neutral points (vertices met by no edge of $V_0$). If
--   $$
--   |N| \le 1,
--   $$
--   then $V_0$ is a maximum matching: no matching of $G$ has more edges than $V_0$.
--
--   This is the base case in Berge's proof of Theorem 1, which then assumes $|N| > 1$.
-- source:
--   Berge, Two theorems in graph theory, Proc. Natl. Acad. Sci. USA 43 (1957), p. 843, Lemma 5

import Mathlib
import Definitions.Def_BergeMatching_Core_AlternatingChain

namespace BergeMatching.Core

/-- Berge (1957), p. 843, Lemma 5: if `|N| ≤ 1`, `V₀` is a maximum matching. -/
theorem lemma_5 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : G.Subgraph) (hM : M.IsMatching) (hN : {x : V | IsNeutral M x}.ncard ≤ 1) :
    IsMaximumMatching M := by sorry

end BergeMatching.Core
