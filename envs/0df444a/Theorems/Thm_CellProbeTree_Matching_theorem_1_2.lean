-- Prove2me | Theorems.Thm_CellProbeTree_Matching_theorem_1_2
-- name    : CellProbeTree.Matching.theorem_1_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:36:27.309396+00:00
-- url     : https://prove2.me/theorems/4c45d36d-80e5-4ecb-b24d-38066f1d2514
-- title:
--   Theorem 1.2 — findopen/findclose with $t$ adaptive probes needs redundancy $r \ge N/w^{O(t)} - O(1)$
-- statement:
--   There are absolute constants $c > 0$, $C > 0$ and $K \ge 0$ with the following property. Let $n \ge 1$, $N = 2n$, and let $w, t \ge 1$ be integers with $w \ge \lceil \log_2 N \rceil$. Consider any static cell-probe data structure for Dyck words $X \in \mathcal D_n$ with $s$ cells of $w$ bits: an arbitrary encoding of $X$ into memory and, for every position $i \in [N]$, a deterministic fully adaptive query algorithm that receives only $i$, returns $\mathrm{findclose}_X(i)$ when $i$ is an opening and $\mathrm{findopen}_X(i)$ when $i$ is a closing, on every $X \in \mathcal D_n$, and makes at most $t$ probes on every input and every position. If its space satisfies $s\,w \le \log_2 C_n + r$ for a real number $r$ (the **redundancy**, $C_n = |\mathcal D_n|$ the Catalan number), then
--   $$r \;\ge\; c\,\frac{N}{w^{C t}} - K .$$
--   This is the paper's $r \ge N/w^{O(t)}$, with exponent linear in $t$: for $w = \Theta(\log n)$ and constant $t$ it matches the $n/\mathrm{polylog}\,n$ redundancy of known upper bounds.
--
--   Differences from the source:
--   - reading: $r \ge N/w^{O(t)}$ (display (1)) → $r \ge c\,N/w^{Ct} - K$ with absolute $c > 0$, $C > 0$, $K \ge 0$ fixed before $n, w, t, s$ and the structure; reason: the paper's §1.2 convention for this shorthand (p. 4: "$r \ge N/w^{O(t)} - O(1)$ means $r \ge cN/w^{Ct} - K$"), its proof ends with $r + 1 \ge N/w^{O(t)}$, and the form without $-K$ is false at $n = 1$ (INSIGHTS I1).
--   - encoding: positions $i \in [N]$ (1-based) → `Fin (2 * n)` (0-based); reason: Lean convention, same instances.
--   - encoding: memory of $s$ words of $w$ bits, adaptive query algorithm, number of probes → `Fin s → BitVec w`, `DynOracleConn.ProbeTree (Fin s) (BitVec w) (Fin (2 * n))`, its `cost` (every probe on the path counted); reason: Lean representation of the cell-probe model; memoizing repeated reads changes no answer and does not increase the count, so the class of structures with at most $t$ probes is the paper's.
-- source:
--   Liang, Liu, Nearly Tight Cell-Probe Lower Bounds for Querying on Tree via Talagrand Inequality, STOC 2027 submission (manuscript sha256 0e5a8eb2…), p. 4, §1.2 and Theorem 1.2, display (1); proved in §4.7, pp. 24–25

import Mathlib
import Definitions.Def_DynOracleConn_ProbeTree
import Definitions.Def_CellProbeTree_Matching_Mate
import Definitions.Def_CellProbeTree_Matching_CellProbe

namespace CellProbeTree.Matching

/-- Theorem 1.2 (Liang–Liu): there are absolute constants `c, C > 0`, `K ≥ 0` such that every
static cell-probe structure for findopen/findclose on Dyck words of length `N = 2n`, with `s` cells
of `w ≥ ⌈log₂ N⌉` bits, an arbitrary encoding and fully adaptive queries of at most `t` probes,
whose space satisfies `s·w ≤ log₂ C_n + r`, has `r ≥ c·N / w^{C·t} − K`. -/
theorem theorem_1_2 :
    ∃ c C K : ℝ, 0 < c ∧ 0 < C ∧ 0 ≤ K ∧
      ∀ (n w t s : ℕ), 1 ≤ n → 1 ≤ w → 1 ≤ t → Nat.clog 2 (2 * n) ≤ w →
        ∀ D : MatchingStructure n s w, D.Correct → D.ProbesAtMost t →
          ∀ r : ℝ, ((s * w : ℕ) : ℝ) ≤ Real.logb 2 (catalan n : ℝ) + r →
            c * ((2 * n : ℕ) : ℝ) / (w : ℝ) ^ (C * (t : ℝ)) - K ≤ r := by sorry

end CellProbeTree.Matching
