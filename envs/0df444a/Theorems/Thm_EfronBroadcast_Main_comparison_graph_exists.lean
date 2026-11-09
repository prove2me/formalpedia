-- Prove2me | Theorems.Thm_EfronBroadcast_Main_comparison_graph_exists
-- name    : EfronBroadcast.Main.comparison_graph_exists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:02:29.348626+00:00
-- url     : https://prove2.me/theorems/3dd8cb46-19b1-47f8-a64d-fca65aa5db6c
-- title:
--   Lemma 2 — sparse comparison graphs
-- statement:
--   There is an absolute constant $C>0$ such that, for every $k\ge0$, $n=2^k$, and integer $1\le c\le n$, a simple graph $G_c$ on $[n]$ satisfies
--
--   $$
--   \deg_{G_c}(v)\le Cck\quad(v\in[n]),\qquad
--   X\cap Y=\varnothing,\ |X|,|Y|\ge n/c
--   \ \Longrightarrow\ E(G_c)\cap(X\times Y)\ne\varnothing.
--   $$
--
--   The same constant works for the entire graph family. These public graphs support request-consistency comparisons in Ladder; no online randomness is asserted. At $n=1$ the edgeless graph satisfies both requirements.
--
--
--   Differences from the source:
--   - encoding: the standing power-of-two convention and O(c log n) degree → n = 2^k and an absolute C with degree at most C c k; reason: k = log₂ n exactly, and the uniform constant is quantified before k and c
--   - encoding: disjoint sets of size at least n/c → Fin indices, Finset disjointness and integer inequalities n ≤ c |X| and n ≤ c |Y|; reason: positive c makes the multiplicative inequalities exactly the source thresholds, without natural-number division
-- source:
--   Yuval Efron, Jovan Komatovic, Ling Ren, Byzantine Broadcast in Õ(n²) Communication, STOC 2027 submission #526 (October 2026), p. 2, PDF p. 3, Lemma 2; pinned local source.pdf, SHA256 626a479d5227c34ed2d6343fdc7113666962d88d8b482e8a2be02db9f8028a0f

import Mathlib
import Definitions.Def_EfronBroadcast_Main_ComparisonGraph
set_option autoImplicit false

namespace EfronBroadcast.Main

/-- Lemma 2, p. 2 (PDF p. 3). A single constant works for the entire family.
The section's power-of-two convention is retained, including n = 1. -/
theorem comparison_graph_exists :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, ∀ c : ℕ, 1 ≤ c → c ≤ 2 ^ k →
      ∃ G : SimpleGraph (Fin (2 ^ k)),
        (∀ v, (comparisonDegree G v : ℝ) ≤ C * c * k) ∧
        ComparisonProperty c G := by sorry

end EfronBroadcast.Main
