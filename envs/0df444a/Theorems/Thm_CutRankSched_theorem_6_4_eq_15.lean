-- Prove2me | Theorems.Thm_CutRankSched_theorem_6_4_eq_15
-- name    : CutRankSched.theorem_6_4_eq_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T13:35:55.243143+00:00
-- url     : https://prove2.me/theorems/2e7dde89-8ce0-44f3-85dc-024fc2135ed7
-- title:
--   Theorem 6.4, Eq. (15) — capacity bound $n\le mL$
-- statement:
--   Let $I$ be a valid instance with $n$ events on $m$ qubits. If $I$ is feasible in at most $L$ conservative rounds, then
--   $$
--   n \le mL. \tag{15}
--   $$
--
--   Every event uses a nonempty exposure region and the regions in one layer are pairwise disjoint, so a layer holds at most $m$ events. The bound gives Algorithm 1 its rejection test (line 3) and, with $L < n$ in the nontrivial case, keeps factors polynomial in $L$ polynomial in $n$.
--
--   Differences from the source:
--   - generalization: a positive integer budget L (Problem 3.2, p.5) → any L : ℕ, L = 0 included; reason: at L = 0 the statement still holds (no layer assignment of a nonempty trace exists, or the bound is trivial); for L ≥ 1 it is the source's claim
--   - encoding: events 1..n and layers [L] = {1..L} → Fin n and Fin L (0-based; event i and layer t are the paper's i+1 and t+1); reason: index shift; same instances and assignments
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Theorem 6.4, Eq. (15), p.12

import Mathlib
import Definitions.Def_CutRankSched_Instance
import Definitions.Def_CutRankSched_Instance_Valid
import Definitions.Def_CutRankSched_Feasible

set_option autoImplicit false

namespace CutRankSched

/-- **Theorem 6.4, Eq. (15) (Capacity of a feasible schedule)** (Zhao–Chen–Li–Kong–Peng–Yu–Yue, *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), Theorem 6.4, Eq. (15),
p.12). If a valid instance is feasible in at most `L` conservative rounds, then `n ≤ mL`.

**Formalization Note** "Feasible in at most `L` rounds" is `Feasible I L` (a map into `Fin L`). -/
theorem theorem_6_4_eq_15 (I : Instance) (L : ℕ) (hI : I.Valid) (hF : Feasible I L) :
    I.n ≤ I.m * L := by sorry

end CutRankSched
