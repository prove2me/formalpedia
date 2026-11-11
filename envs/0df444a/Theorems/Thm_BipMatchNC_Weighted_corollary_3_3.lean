-- Prove2me | Theorems.Thm_BipMatchNC_Weighted_corollary_3_3
-- name    : BipMatchNC.Weighted.corollary_3_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:15:12.408474+00:00
-- url     : https://prove2.me/theorems/2b1425d8-53f6-4431-837b-1ba1377f7421
-- title:
--   Corollary 3.3: bipartite perfect matching (decision) is in logspace-uniform NC²
-- statement:
--   The language of (codes of) balanced bipartite graphs that have a perfect matching is in logspace-uniform $\mathrm{NC}^2$: there are a constant $c$ and a logspace-uniform family $(C_N)$ of fan-in-2 Boolean circuits with $\mathrm{size}(C_N)\le N^c+c$ and
--   $$\mathrm{depth}(C_N)\le c\lfloor\log_2N\rfloor^2+c$$
--   such that $C_{|x|}(x)=1$ if the word $x$ is the code of a balanced bipartite graph with a perfect matching, and $C_{|x|}(x)=0$ for every other word $x$. A graph on $[n]+[n]$ is coded by the self-delimiting code of $n$ followed by its $n^2$ adjacency bits.
--
--   This is the first deterministic $\mathrm{NC}$ algorithm for bipartite perfect matching decision; it follows from Theorem 3.1 and the $\mathrm{NC}^2$ rank algorithms of Berkowitz and Csanky.
--
--   Differences from the source:
--   - encoding: in NC^k: logspace-uniform polynomial-size Boolean circuits of depth O(log^k n), n the input length → one constant c, a family C : ∀ N, BoolCircuit N (fan-in ≤ 2) with LogspaceUniform C, size ≤ N^c + c, depth ≤ c·⌊log₂ N⌋^k + c, all fixed before the input; reason: the §2 definition with the O(·) made an explicit constant; fan-in 2 is the usual convention for NC, and logspace uniformity uses the published transducer model
--   - encoding: bipartite perfect matching (decision) → the language PMLanguage of words encGraph G (encNat n, then n² adjacency bits row-major) of graphs G with G.HasPM; every other word, including non-codes, is rejected; reason: only balanced graphs have perfect matchings (p. 4); the decision problem is a language over {0,1}
-- source:
--   Chatterjee, Ghosh, Gurjar, Raj, Thierauf, Bipartite Matching is in NC, STOC 2027 submission (manuscript sha256 c61e59cb…), p. 12 (PDF 13), Corollary 3.3

import Mathlib
import Definitions.Def_BipMatchNC_Weighted_NC
import Definitions.Def_BipMatchNC_Weighted_Problems

namespace BipMatchNC.Weighted

theorem corollary_3_3 : LangInNC 2 PMLanguage := by sorry

end BipMatchNC.Weighted
