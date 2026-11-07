-- Prove2me | Theorems.Thm_FewInnerTSP_lemma_3_1
-- name    : FewInnerTSP.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:34:05.500748+00:00
-- url     : https://prove2.me/theorems/74def1e2-c0b2-43d5-808e-37bf31723a2b
-- title:
--   Lemma 3.1 (Retaining gaps)
-- statement:
--   Let $P$ be $n\ge3$ points in general position with $k>0$ interior points, and $h_0,\dots,h_{h-1}$ a counterclockwise hull order. Let $R$ be the retained gap set of App. A: for every ordered pair $(p,q)$ of interior points, $p=q$ allowed, the $\min\{k,h\}$ gaps $j$ of smallest attachment weight
--   $$w_j(p,q)=|h_jp|+|qh_{j+1}|-|h_jh_{j+1}|$$
--   (ties by index), united over all pairs. Then:
--
--   1. $|R|\le k^3$, and some shortest tour has the chain form (5) with every chain outside $R$ empty: no interior point lies in a non-retained gap.
--   2. There are an admissible real-RAM program and a constant $C$, fixed before the input, such that on the input $(h,k,$ hull points in counterclockwise order, interior points$)$ the program halts within $C(hk^2+k^3)$ steps and outputs the $h$ cells of the $0/1$ indicator of $R$, in hull order.
--
--   The lemma removes the large hull from the exponential part: only $O(k^3)$ insertion gaps need to be considered.
--
--   **Formalization Note** The indicator output needs no ordering of the retained indices, the step the printed count leaves aside.
--
--   Differences from the source:
--   - generalization: one can retain at most k³ hull gaps so that some optimal tour has no interior point in any other gap → App. A's explicit set R = retainedGaps has at most k³ elements and has this property; reason: the explicit set is the one the page's selection computes, and it implies the existence claim
--   - reading: a real-arithmetic model supporting exact Euclidean distances and exact comparison of finite sums of edge costs (no instruction set named) → the published real RAM MatMulTimeLP.RealRAM restricted by Admissible: rational literals, no draws, rsqrt allowed, every executed instruction (index bookkeeping and input reads included) costing 1; reason: the fewest primitives give the strongest statement under an existential program; comparing a sum costs its additions plus one comparison, which no model with those primitives undercuts
--   - encoding: O(hk² + k³) arithmetic operations, apart from ordering the retained indices → (t+1) ≤ C (h k² + k³) with C fixed before the input, output the 0/1 indicator of R in hull order; reason: the indicator is the selection without the ordering step
--   - encoding: the hull and interior points as data → the input (h, k, hull coordinates in counterclockwise order, interior coordinates in any order); reason: a machine statement needs a layout
--   - encoding: a set of points in the plane → an indexed list P : Fin n → EuclideanSpace ℝ (Fin 2), with general position over distinct indices and no separate distinctness hypothesis; reason: no three collinear forces distinct points for n ≥ 3; the Euclidean, not the sup, metric
-- source:
--   Li, Ma, Gong, Exact Euclidean TSP with Few Interior Points: A Square-Root Exponent, STOC 2027 submission (manuscript sha256 6541f631…), Lemma 3.1, p.4 (PDF p.6); proof App. A, p.16 (PDF p.18)

import Mathlib
import Definitions.Def_FewInnerTSP_HullOrder
import Definitions.Def_FewInnerTSP_RetainedGaps
import Definitions.Def_FewInnerTSP_Admissible
import Definitions.Def_FewInnerTSP_Layouts

namespace FewInnerTSP

/-- **Lemma 3.1 (Retaining gaps).** Li, Ma, Gong, *Exact Euclidean TSP with Few Interior Points: A
Square-Root Exponent*, STOC 2027 submission (manuscript sha256 6541f631…), Lemma 3.1, p.4 (PDF p.6),
proof in App. A, p.16 (PDF p.18): "For k > 0 one can retain at most k³ hull gaps so that some optimal
tour has no interior point in any other gap. The selection uses O(hk² + k³) arithmetic operations, apart
from ordering the retained indices if needed."

The retained set is App. A's `R = retainedGaps P hull`, the union over ordered interior pairs `(p, q)`,
`p = q` included, of the `min{k, h}` cheapest gaps under `w_j(p, q)` with ties by index.
1. (`k > 0`) `|R| ≤ k³`, and some shortest tour has the form (5) with every chain outside `R` empty.
2. One admissible program and a constant `C`, fixed before the input, on the input `[h, k]`, the hull
   in counterclockwise order and the interior points (in any order), halt within `C (h k² + k³)` steps
   and output the `h` cells of the `0/1` indicator of `R` in hull order.

**Formalization Note** The indicator output needs no ordering step, which is the step the printed count
leaves aside. Gap `j` is the gap between `h_j` and `h_{j+1}` (cyclic). -/
theorem lemma_3_1 :
    (∀ (n : ℕ), 3 ≤ n → ∀ P : Fin n → Pt, GeneralPos P → ∀ (h : ℕ) (hull : Fin h → Fin n),
      IsHullOrder P hull → 0 < interiorCount P →
      (retainedGaps P hull).card ≤ interiorCount P ^ 3 ∧
      ∃ (π : Equiv.Perm (Fin n)) (S : Fin h → List (Fin n)), IsShortestTour P π ∧
        HasChainForm P hull S π ∧ ∀ j, j ∉ retainedGaps P hull → S j = []) ∧
    (∃ A : MatMulTimeLP.Program, Admissible A ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ), 3 ≤ n → ∀ P : Fin n → Pt, GeneralPos P → ∀ (h : ℕ) (hull : Fin h → Fin n),
      IsHullOrder P hull → 0 < interiorCount P → ∀ I : List (Fin n), IsListing I (interiorIdx P) →
      ∀ ω : MatMulTimeLP.Tape, ∃ t : ℕ, MatMulTimeLP.HaltsAt A (gapLayout P hull I) ω t ∧
        (t : ℝ) + 1 ≤ C * ((h : ℝ) * (interiorCount P : ℝ) ^ 2 + (interiorCount P : ℝ) ^ 3) ∧
        OutputIs A (gapLayout P hull I) ω t
          (List.ofFn fun j : Fin h => if j ∈ retainedGaps P hull then (1 : ℝ) else 0)) := by sorry

end FewInnerTSP
