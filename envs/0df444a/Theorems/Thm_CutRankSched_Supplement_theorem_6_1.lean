-- Prove2me | Theorems.Thm_CutRankSched_Supplement_theorem_6_1
-- name    : CutRankSched.Supplement.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:53:26.753577+00:00
-- url     : https://prove2.me/theorems/808f6729-a190-4b92-86ed-2a20f1856187
-- title:
--   Theorem 6.1 — support–rank–coloring bound
-- statement:
--   Let an instance have nonidentity Paulis $p_i\neq0$ and support containment $\mathrm{supp}(p_i)\subseteq V(T_i)$ for every event; connectedness of the exposures and feasibility are not assumed. With $\chi(X^\circ)$ the chromatic number of the residual conflict graph, $r=\mathrm{rank}_{\mathbb F_2}A$ and $w^\circ$ the vertex-separation width of $X^\circ$ in the given order,
--   $$
--   n \le m\,\chi(X^\circ)(r+1) \le m(w^\circ+1)(r+1) \le m(w^\circ+1)(2m+1). \tag{13}
--   $$
--
--   The bound holds for every input, feasible or not, and limits how many events a small hardware graph with a narrow residual frontier can carry.
--
--   **Formalization Note** The chain is stated in $\mathbb N\cup\{\infty\}$, where Mathlib's chromatic number lives (it is finite here).
--
--   Differences from the source:
--   - generalization: any valid instance with nonempty Pauli supports and support containment (valid includes connected exposures) → only p_i ≠ 0 and supp(p_i) ⊆ V(T_i); connectedness is not assumed; reason: the theorem states the first inequality needs no connected exposures; the other two hold for every instance; valid instances are a special case
--   - encoding: the chain (13) of natural numbers with the chromatic number χ(X°) → the chain in ℕ∞ with SimpleGraph.chromaticNumber of residualGraph I; reason: Mathlib's chromatic number is ℕ∞-valued; it is finite on a finite graph
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Theorem 6.1, Eq. (13), p.11

import Mathlib
import Definitions.Def_CutRankSched_Instance
import Definitions.Def_CutRankSched_supp
import Definitions.Def_CutRankSched_A
import Definitions.Def_CutRankSched_width
import Definitions.Def_CutRankSched_Supplement_residualGraph

set_option autoImplicit false

namespace CutRankSched

namespace Supplement

/-- **Theorem 6.1 (Support–rank–coloring)** (Zhao et al., *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), Theorem 6.1, Eq. (13), p.11). For any instance
with nonempty Pauli supports and support containment,
`n ≤ m χ(X°)(r + 1) ≤ m(w° + 1)(r + 1) ≤ m(w° + 1)(2m + 1)` (13).
The first inequality does not require connected exposures or a feasible schedule.

**Formalization Note** Hypotheses are only `p_i ≠ 0` and `supp(p_i) ⊆ V(T_i)` (no connectedness).
`χ(X°)` is Mathlib's `chromaticNumber : ℕ∞` of `residualGraph I`; the chain is stated in `ℕ∞`.
`r = rank_{𝔽₂} A`. -/
theorem theorem_6_1 (I : Instance)
    (hp : ∀ i, I.p i ≠ 0) (hsupp : ∀ i, (↑(supp (I.p i)) : Set (Fin I.m)) ⊆ (I.T i).verts) :
    (I.n : ℕ∞) ≤ I.m * (residualGraph I).chromaticNumber * ((A I).rank + 1) ∧
      (I.m : ℕ∞) * (residualGraph I).chromaticNumber * ((A I).rank + 1) ≤
        I.m * (width I + 1) * ((A I).rank + 1) ∧
      (I.m : ℕ∞) * (width I + 1) * ((A I).rank + 1) ≤ I.m * (width I + 1) * (2 * I.m + 1) := by sorry

end Supplement

end CutRankSched
