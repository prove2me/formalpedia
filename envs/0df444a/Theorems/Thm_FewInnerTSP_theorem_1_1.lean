-- Prove2me | Theorems.Thm_FewInnerTSP_theorem_1_1
-- name    : FewInnerTSP.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:26:39.568657+00:00
-- url     : https://prove2.me/theorems/c1b7bb03-6d86-430f-8608-b1ec098b6d15
-- title:
--   Theorem 1.1 (Arithmetic upper bound): a shortest Euclidean tour in $O(n\log n+nk^2+2^{O(\sqrt k)})$ real-RAM operations
-- statement:
--   There are a deterministic real-RAM program and constants $C,c>0$, fixed before the input, with the following property. For every $n\ge3$ and every set $P$ of $n$ points in the plane in general position (no three collinear), with **arbitrary real coordinates** and $k$ strict interior points ($k=|P\setminus\mathrm{vert}(\mathrm{CH}(P))|$), the program, run on the coordinates of $P$, halts within
--   $$C\Bigl(n\log n+nk^2+2^{c\sqrt k}\Bigr)$$
--   operations and outputs a shortest Euclidean Hamiltonian cycle of $P$, as the order $\pi(0),\pi(1),\dots,\pi(n-1)$ in which it visits the points.
--
--   The machine is a real-arithmetic model with exact addition, subtraction, multiplication, division, square roots (hence exact Euclidean distances) and comparisons (hence exact comparison of finite sums of edge costs), unit cost per operation.
--
--   The bound improves the interior-point dependence of exact Euclidean TSP from $k^{O(\sqrt k)}=2^{O(\sqrt k\log k)}$ (Gawrychowski–Rusak) to $2^{O(\sqrt k)}$, with the hull vertices entering only through polynomial preprocessing; for $k=\Theta(n)$ it matches the known $2^{O(\sqrt n)}$.
--
--   **Formalization Note** The model is the published real RAM `MatMulTimeLP.RealRAM` restricted to admissible programs (rational literals, no random draws). Every executed instruction costs one step, including index bookkeeping and input reads; there is no floor. The input is $(n,x_0,y_0,\dots)$; the output cells hold $\pi(j)$ as reals, 0-based.
--
--   Differences from the source:
--   - reading: a real-arithmetic model supporting exact Euclidean distances and exact comparison of finite sums of edge costs (no instruction set named) → the published real RAM MatMulTimeLP.RealRAM restricted by Admissible: rational literals, no draws, rsqrt allowed, every executed instruction (index bookkeeping and input reads included) costing 1; reason: the fewest primitives give the strongest statement under an existential program; comparing a sum costs its additions plus one comparison, which no model with those primitives undercuts
--   - encoding: O(n log n + nk² + 2^{O(√k)}) operations → (t+1) ≤ C (n log n + n k² + 2^{c√k}), with the program and C, c fixed before n and P; reason: O-notation with two constants before the input; the natural logarithm differs from any other base by a constant in C
--   - encoding: the algorithm returns a tour, not only its value → the first n output cells hold π(0), …, π(n−1) of a permutation π whose cyclic order is a shortest tour; reason: a machine statement needs an output layout
--   - encoding: k strict interior points → k = |P \ vert(CH(P))| via the extreme points of the convex hull; reason: the page's definition (§1, p.1); in general position the two agree
--   - encoding: deterministically → the conclusion holds on every random tape of the machine, and admissible programs have no draws; reason: the machine is deterministic on admissible programs
--   - encoding: a set of points in the plane → an indexed list P : Fin n → EuclideanSpace ℝ (Fin 2), with general position over distinct indices and no separate distinctness hypothesis; reason: no three collinear forces distinct points for n ≥ 3; the Euclidean, not the sup, metric
-- source:
--   Li, Ma, Gong, Exact Euclidean TSP with Few Interior Points: A Square-Root Exponent, STOC 2027 submission (manuscript sha256 6541f631…), Theorem 1.1, p.1 (PDF p.3)

import Mathlib
import Definitions.Def_FewInnerTSP_Instance
import Definitions.Def_FewInnerTSP_Admissible

namespace FewInnerTSP

/-- **Theorem 1.1 (Arithmetic upper bound).** Li, Ma, Gong, *Exact Euclidean TSP with Few Interior
Points: A Square-Root Exponent*, STOC 2027 submission (manuscript sha256 6541f631…), Theorem 1.1, p.1
(PDF p.3): "For a general-position planar set P with n points and k strict interior points, a shortest
Euclidean Hamiltonian cycle can be computed deterministically in O(n log n + nk² + 2^{O(√k)}) operations
in a real-arithmetic model supporting exact Euclidean distances and exact comparison of finite sums of
edge costs. The algorithm returns a tour, not only its value."

There is one admissible program of the published real RAM and constants `C, c > 0`, fixed before the
input, such that on every instance of `n ≥ 3` general-position points with arbitrary real coordinates
the run halts within `C (n log n + n k² + 2^{c √k})` steps and leaves in its first `n` output cells the
values `π 0, …, π (n−1)` of a permutation `π` whose cyclic order is a shortest tour.

**Formalization Note**
* The machine is `MatMulTimeLP.RealRAM` restricted by `Admissible`: rational literals, no Gaussian or
  uniform draw, `rsqrt` allowed. Every executed instruction costs `1`, including index bookkeeping and
  input reads; the machine has no floor and no real-to-index cast. Removing instructions only
  strengthens an `∃ program` statement.
* The input is `layout P`: the real `n`, then the two coordinates of each point. The tape argument `ω`
  is irrelevant for an admissible program (no draws) and is quantified universally.
* `HaltsAt A input ω t` says the run halts at step `t`; the running time is `t + 1`.
* `k = interiorCount P = |P \ vert(CH(P))|`, the page's `I`. General position makes it the number of
  strict interior points. `Real.log` differs from any other base by a constant absorbed in `C`.
* The output is the tour as a permutation, encoded 0-based. -/
theorem theorem_1_1 :
    ∃ A : MatMulTimeLP.Program, Admissible A ∧ ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (n : ℕ), 3 ≤ n → ∀ P : Fin n → Pt, GeneralPos P →
      ∀ ω : MatMulTimeLP.Tape, ∃ t : ℕ, MatMulTimeLP.HaltsAt A (layout P) ω t ∧
        (t : ℝ) + 1 ≤ C * ((n : ℝ) * Real.log n + (n : ℝ) * (interiorCount P : ℝ) ^ 2 +
          (2 : ℝ) ^ (c * Real.sqrt (interiorCount P : ℝ))) ∧
        ∃ π : Equiv.Perm (Fin n),
          (∀ j : Fin n, MatMulTimeLP.outputAt A (layout P) ω t n j = ((π j : ℕ) : ℝ)) ∧
          IsShortestTour P π := by sorry

end FewInnerTSP
