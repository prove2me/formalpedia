-- Prove2me | Theorems.Thm_DynApproxIdx_Main_fact_8_3
-- name    : DynApproxIdx.Main.fact_8_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:52:57.331204+00:00
-- url     : https://prove2.me/theorems/758804b2-e598-4c77-a628-b17280821ac2
-- title:
--   Fact 8.3 — deletion-only orthogonal range reporting: O(n log n) preprocessing, O(log² n) deletion, O(log² n + output) report
-- statement:
--   A set of $n$ points in the plane, each with a value, can be preprocessed in $O(n\log n)$ time so that a point can be deleted in $O(\log^2 n)$ time and the remaining points in an axis-parallel rectangle can be reported in $O(\log^2 n+\mathrm{output})$ time.
--
--   Precisely: there are one program $P$ of the word RAM, a constant $C$ and a width constant $c_w$ such that, for every list of $n$ points with values, every valid sequence of deletions and reports, every word size $w\ge c_w\lceil\log_2(\sigma_{\max}+3)\rceil$ and every coin tape,
--   $$\mathrm{time}_0\le C(n+1)\log_2(n+2),\qquad \mathrm{time}_{\mathrm{del}}\le C\log_2^2(n+2),\qquad \mathrm{time}_{\mathrm{rep}}\le C\bigl(\log_2^2(n+2)+\mathrm{output}\bigr),$$
--   and every report writes the identifiers of the present points in its rectangle, each exactly once, where $\mathrm{output}$ is their number.
--
--   It is the range-reporting structure behind the dynamic $k$-errata trees of §8 (Corollary 6.10).
--
--   Differences from the source:
--
--   - reading: O(n log n), O(log² n), O(log² n + output) time → explicit universal C with log₂(n + 2): C(n+1)log₂(n+2), C·log₂(n+2)², C(log₂(n+2)² + output); n the number of points given at preprocessing; reason: log₂(n + 2) ≥ 1 keeps the bounds meaningful at n ≤ 1 and is within a constant factor of log n for n ≥ 2
--   - reading: the bounds (no randomness mentioned) → worst case on every coin tape, for one program; reason: Fact 8.3 is a deterministic range tree statement
--   - encoding: points in the plane with values; report the remaining points → points (x_i, y_i, v_i) ∈ ℕ³ given as words and identified by their index; a report writes each identifier of a present point in [a,b] × [c,d] exactly once; reason: inputs of a word RAM are words; an identifier gives the point and its value; the paper applies the fact to integer ranks
--   - encoding: the machine model (unstated) → the published word RAM DynBrooks_Machine with the online protocol of Run, w ≥ c_w ⌈log₂(σ_max + 3)⌉; reason: standard word RAM with Θ(log)-bit words for the given numbers
-- source:
--   Charalampopoulos, Ellert, Radoszewski, Dynamic Approximate Text Indexing, STOC 2027 submission (manuscript sha256 7f902057…), p. 44 (PDF 46), Fact 8.3

import Mathlib
import Definitions.Def_DynBrooks_Machine
import Definitions.Def_DynApproxIdx_Main_Run
import Definitions.Def_DynApproxIdx_Main_RangeReport

namespace DynApproxIdx.Main

/-- **Fact 8.3** (Charalampopoulos, Ellert, Radoszewski, *Dynamic Approximate Text Indexing*, STOC
2027 submission, p. 44 (PDF 46)). A set of `n` points in the plane (each with a value) can be
preprocessed in `O(n log n)` time so that a point can be deleted in `O(log² n)` time and the
remaining points in an axis-parallel rectangle can be reported in `O(log² n + output)` time: there
are one program `P`, a constant `C` and a width constant `c_w` such that for every list of `n`
points, every valid sequence of deletions and reports, every word size
`w ≥ c_w ⌈log₂(σ_max + 3)⌉` and every coin tape, the preprocessing takes at most
`C (n + 1) log₂(n + 2)` steps, each deletion at most `C log₂(n + 2)²` steps, and each report at most
`C (log₂(n + 2)² + output)` steps, where `output` is the number of reported points, and writes the
identifiers of the remaining points in the rectangle, each exactly once. -/
theorem fact_8_3 :
    ∃ (P : DynBrooks.Program) (C : ℝ) (cw : ℕ),
      ∀ (pts : List (ℕ × ℕ × ℕ)) (ops : List RROp), RRValidFrom {i | i < pts.length} ops →
        ∀ w : ℕ, cw * rrWidth pts ops ≤ w → ∀ ω : ℕ → BitVec w,
          LeReal (opTime P ω (pointWords pts) (ops.map RROp.words) 0)
              (C * ((pts.length : ℝ) + 1) * Real.logb 2 ((pts.length : ℝ) + 2)) ∧
          ∀ j : ℕ, j < ops.length →
            (∀ i : ℕ, ops[j]? = some (.del i) →
              LeReal (opTime P ω (pointWords pts) (ops.map RROp.words) (j + 1))
                (C * Real.logb 2 ((pts.length : ℝ) + 2) ^ 2)) ∧
            (∀ a b c d : ℕ, ops[j]? = some (.report a b c d) →
              LeReal (opTime P ω (pointWords pts) (ops.map RROp.words) (j + 1))
                (C * (Real.logb 2 ((pts.length : ℝ) + 2) ^ 2 +
                  ((inRect pts (presentAt pts.length ops j) a b c d).ncard : ℝ))) ∧
              ∃ out : List ℕ, opOutput P ω (pointWords pts) (ops.map RROp.words) (j + 1) = some out ∧
                out.Nodup ∧ ∀ i : ℕ, i ∈ out ↔ i ∈ inRect pts (presentAt pts.length ops j) a b c d) := by sorry

end DynApproxIdx.Main
