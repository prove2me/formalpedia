-- Prove2me | Theorems.Thm_CutRankSched_section_5_1_trivial_cases
-- name    : CutRankSched.section_5_1_trivial_cases
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T13:36:17.095198+00:00
-- url     : https://prove2.me/theorems/a401a8bf-fa73-45b3-ae91-a2531082fe4d
-- title:
--   Section 5.1 — the trivial cases $n=0$, $L\ge n$, $n>mL$
-- statement:
--   For every instance and budget $L$:
--
--   1. if $n = 0$, the instance is feasible (with zero rounds);
--   2. if $L \ge n$, the assignment $\lambda_i = i$ satisfies (2);
--   3. if the instance is valid and $n > mL$, it is infeasible;
--   4. hence, for a positive integer $L$, in the remaining case $n \ne 0$ and $L < n$ one has $1 \le L < n$.
--
--   These are the guards of lines 1–4 of Algorithm 1.
--
--   Differences from the source:
--   - generalization: a positive integer budget L (Problem 3.2, p.5) → any L : ℕ, L = 0 included; reason: at L = 0 the statement still holds (no layer assignment of a nonempty trace exists, or the bound is trivial); for L ≥ 1 it is the source's claim
--   - generalization: stated for valid instances (Section 3.1's standing assumptions) → every instance, valid or not; reason: clauses 1, 2 and 4 hold for every instance; clause 3 keeps the validity hypothesis; valid instances are a special case
--   - encoding: events 1..n and layers [L] = {1..L} → Fin n and Fin L (0-based; event i and layer t are the paper's i+1 and t+1); reason: index shift; same instances and assignments
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Section 5.1, p.8

import Mathlib
import Definitions.Def_CutRankSched_Instance
import Definitions.Def_CutRankSched_Instance_Valid
import Definitions.Def_CutRankSched_IsSchedule
import Definitions.Def_CutRankSched_Feasible

set_option autoImplicit false

namespace CutRankSched

/-- **Section 5.1, trivial cases** (Zhao–Chen–Li–Kong–Peng–Yu–Yue, *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), §5.1, p.8). If `n = 0` the instance is feasible
(with zero rounds); if `L ≥ n`, the assignment `λ_i = i` is feasible; if `n > mL`, a valid
instance is infeasible; hence in the remaining case `1 ≤ L < n`.

**Formalization Note** 0-based: `λ_i = i` is `fun i => ⟨i.val, _⟩ : Fin n → Fin L`. The last
clause takes the paper's standing `1 ≤ L` ("a positive integer `L`", Problem 3.2). -/
theorem section_5_1_trivial_cases (I : Instance) (L : ℕ) :
    (I.n = 0 → Feasible I L) ∧
    (∀ h : I.n ≤ L, IsSchedule I L (fun i => ⟨i.val, lt_of_lt_of_le i.isLt h⟩)) ∧
    (I.Valid → I.m * L < I.n → ¬ Feasible I L) ∧
    (1 ≤ L → I.n ≠ 0 → ¬ I.n ≤ L → 1 ≤ L ∧ L < I.n) := by sorry

end CutRankSched
