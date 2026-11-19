-- Prove2me | Theorems.Thm_DecrAlmostLinearSSSP_Decremental_exact_small_accuracy_sssp
-- name    : DecrAlmostLinearSSSP.Decremental.exact_small_accuracy_sssp
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T10:39:20.611956+00:00
-- url     : https://prove2.me/theorems/c3b99322-c4da-476f-bc42-fff90885e7da
-- title:
--   Charged exact recomputation for small accuracy
-- statement:
--   There is one deterministic scalar RAM program for all valid decremental source-distance inputs with accuracy $0<\epsilon\le1/m$. For an absolute positive constant $C$ and a positive subpolynomial function $a$, its total charged work over every legal deletion stream satisfies
--
--   $$
--   \operatorname{work}\le Cma(m)\epsilon^{-1}\max(1,\log_2 W).
--   $$
--
--   After initialization and every completed deletion, it stores simultaneous multiplicative distance estimates and identifies unreachable vertices exactly. Every operation terminates, and a stored-array query takes nine charged instructions. All graph access, recomputation, queue operations, and array writes are charged in the scalar RAM model.
--
--   This is the small-accuracy branch of the general-domain reduction, where the factor $\epsilon^{-1}$ absorbs exact recomputation.
-- source:
--   Cui, Li, Miao and Wang, Partially Dynamic Single-Source Shortest Paths in Almost-Linear Time, October 2026 submission #912, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/912.pdf, p.4, unnumbered exact-recomputation reduction for epsilon at most 1/m. Exact shortest paths are implemented by Dijkstra label setting with a native radix-trie priority queue.

import Mathlib
import Definitions.Def_DecrAlmostLinearSSSP_Decremental_Adapters
set_option autoImplicit false
open scoped ENNReal NNReal
open DecrAlmostLinearSSSP.Decremental

theorem DecrAlmostLinearSSSP.Decremental.exact_small_accuracy_sssp :
    ∃ (p : Program) (C : ℝ) (a : ℕ → ℝ),
    0 < C ∧ Subpolynomial a ∧ ∀ i : Input, i.Valid →
      i.accuracy ≤ 1/(i.size : ℝ) → Maintains p C a 9 true i := by sorry
