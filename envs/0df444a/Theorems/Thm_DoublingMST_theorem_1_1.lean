-- Prove2me | Theorems.Thm_DoublingMST_theorem_1_1
-- name    : DoublingMST.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:35:46.001627+00:00
-- url     : https://prove2.me/theorems/c3d5d2e4-75b9-436c-a738-4ca6d593fa06
-- title:
--   Theorem 1.1 — deterministic $(1+\epsilon)$-MST in time $2^{O(\mathrm{ddim})}(n\log n+\min\{n^2,\frac{n}{\epsilon}\log\frac1\epsilon\})$
-- statement:
--   There are a program $P$ of the real RAM with unit-cost exact-distance oracle of Definition 2.1 and an absolute constant $C>0$ such that the following holds for every $n\ge2$, every injective labelling $\iota$ of $n$ points by integers, every metric $d$ on the points and every $\epsilon\in(0,1/2)$. Started on the labels and $\epsilon$, with oracle $d$, the program halts within
--
--   $$2^{C\cdot\operatorname{ddim}(X)}\Bigl(n\log_2n+\min\Bigl\{n^2,\ \frac{n}{\epsilon}\log_2\frac1\epsilon\Bigr\}\Bigr)$$
--
--   steps and outputs $n-1$ pairs of labels forming a spanning tree of $X$ of weight at most $(1+\epsilon)\,\mathrm{MST}(X)$.
--
--   The program is deterministic, fixed before the input, and is not told $\operatorname{ddim}(X)$. The bound is matched by the paper's lower bound (Theorem 1.3) for doubling dimension $\le7$.
--
--   Differences from the source:
--
--   - encoding: an n-point metric space (X, d) → points Fin n with d : Fin n → Fin n → ℝ satisfying IsMetric; reason: finite metric spaces up to relabelling; same instances
--   - encoding: the standing assumption |X| ≥ 2 of §2 (p.11) → hypothesis 2 ≤ n on the number of points; reason: the source assumes it throughout; it excludes only the one-point space
--   - reading: 2^{O(ddim)} → ∃ C > 0, chosen before the input, with factor 2^{C · ddim(X)}; reason: the standard meaning of the O; ddim(X) ≥ 1 for n ≥ 2, so 2^{C·ddim} also absorbs constant factors
--   - encoding: log → Real.logb 2; reason: the paper's logarithms are base 2 (e.g. 2^{−5 log(1/ϵ)} = ϵ^5, p.21)
--   - encoding: deterministic algorithm in the real RAM model of Definition 2.1 → one fixed program of DoublingMST.Machine, which has no random instruction; time = number of executed instructions, each costing 1; reason: Definition 2.1's unit-cost model
--   - reading: "ordinary RAM operations" on integer registers → integer constants, copy, +, −, increment, decrement, comparison and indirect load/store over unbounded ℤ; no integer ×, ÷ or bit operations; reason: a subset of every ordinary RAM's operations, so an existence claim over it is the stronger one
--   - encoding: n distinct point labels and an oracle d(x, y) on labels → an injective ι : Fin n → ℤ; the oracle instruction returns d on labels, and a non-label argument leaves the run stuck; reason: Definition 2.1's input; the stuck case excludes an undefined call
--   - encoding: a list of n − 1 pairs of point labels stored in integer registers → integer memory cells I[−2i−1], I[−2i−2] at halt; input labels in I[0..n−1], n in p[0], ϵ in r[0]; reason: a fixed layout
--   - encoding: computes a (1 + ϵ)-approximation to MST → IsApproxMST: n − 1 label pairs naming a spanning tree of weight ≤ (1 + ϵ)·MST(X); reason: §1's definition of the problem
--   - reading: "Let ϵ ∈ (0, 1/2). There is a deterministic algorithm …" → one program P and one C, chosen before ϵ (∃ P, ∃ C, ∀ … ∀ ϵ ∈ (0, 1/2)); reason: Definition 2.1 supplies accuracy parameters as exact real inputs, so the algorithm takes ϵ as input; one algorithm for every ϵ specializes to the printed order
-- source:
--   Höckendorff, Hommelsheim, Sohler, Yue, Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics, STOC 2027 submission (manuscript sha256 4855d6b39caaedcdac985f11ec23b5833ef4686c045f97ef13a21bdff2fbe759), Theorem 1.1, p.2 (PDF p.4), restated p.17 (PDF p.19); proof §4.4, p.27 (PDF p.29)

import Mathlib
import Definitions.Def_DoublingMST_Machine
import Definitions.Def_DoublingMST_IsMetric
import Definitions.Def_DoublingMST_ddim
import Definitions.Def_DoublingMST_IsApproxMST
open scoped Classical

namespace DoublingMST

/-- **Theorem 1.1 (deterministic (1 + ϵ)-MST in doubling metrics).**
Höckendorff–Hommelsheim–Sohler–Yue, *Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics*, STOC 2027 submission (manuscript sha256 4855d6b3…be759), Theorem 1.1, p.2 (PDF p.4), restated p.17: "Let ϵ ∈ (0, 1/2). There is a deterministic
algorithm in the real RAM model with a unit-cost exact-distance oracle of Definition 2.1 that, given
as input an n-point metric space (X, d) with doubling dimension ddim, computes a
(1 + ϵ)-approximation to MST in time 2^{O(ddim)}(n log n + min{n², (n/ϵ) log(1/ϵ)})."

There are a program `P` of the real RAM of Definition 2.1 and an absolute `C > 0` such that for
every `n ≥ 2`, every injective labelling `ι : Fin n → ℤ`, every metric `d` on the points and every
`ϵ ∈ (0, 1/2)`, the program started on `(ι, ϵ)` with oracle `d` halts within
$$2^{C\,\mathrm{ddim}(X)}\bigl(n\log_2 n + \min\{n^2, (n/\epsilon)\log_2(1/\epsilon)\}\bigr)$$
steps and outputs `n − 1` pairs of labels forming a spanning tree of weight at most
`(1 + ϵ) · MST(X)`.

**Formalization Note.** `P` is one fixed finite program, chosen before `n`, the labels, the metric
and `ϵ`; it is deterministic (the language has no coins) and is not given ddim. Labels are arbitrary
distinct integers. `2^{O(ddim)}` is one absolute `C` in `2^{C·ddim}`; since `ddim ≥ 1` for `n ≥ 2`,
this absorbs constant factors. Logs are base 2. Machine conventions: `Definitions.Def_DoublingMST_Machine`. -/
theorem theorem_1_1 : ∃ P : Program, ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ), 2 ≤ n → ∀ ι : Fin n → ℤ, Function.Injective ι →
    ∀ d : Fin n → Fin n → ℝ, IsMetric d → ∀ ϵ : ℝ, 0 < ϵ → ϵ < 1 / 2 →
      ∃ out : List (ℤ × ℤ),
        HaltsWithin P ι d ϵ ((2 : ℝ) ^ (C * ddim d) *
          ((n : ℝ) * Real.logb 2 n + min ((n : ℝ) ^ 2) ((n : ℝ) / ϵ * Real.logb 2 (1 / ϵ)))) out ∧
        IsApproxMST d ι ϵ out := by sorry

end DoublingMST
