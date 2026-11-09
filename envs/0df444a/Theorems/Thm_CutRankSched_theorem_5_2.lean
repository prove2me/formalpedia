-- Prove2me | Theorems.Thm_CutRankSched_theorem_5_2
-- name    : CutRankSched.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T13:38:12.493197+00:00
-- url     : https://prove2.me/theorems/1eee4830-07bd-4e19-ba24-68bacad62087
-- title:
--   Theorem 5.2 — the cut-rank DP decides $L$-round feasibility in time $2^{O(\kappa_\pi^2)}(L+1)^{\kappa_\pi}L^{w^\circ+1}\mathrm{poly}(n,m)$
-- statement:
--   **Theorem 5.2 (Cut-rank scheduling DP).** The dynamic program of Algorithm 1 decides Problem 3.2 exactly. Its time and space are, respectively,
--   $$
--   T_{\mathrm{cut}} = 2^{O(\kappa_\pi^2)}(L+1)^{\kappa_\pi}L^{w^\circ+1}\operatorname{poly}(n, m), \qquad S_{\mathrm{cut}} = 2^{O(\kappa_\pi^2)}(L+1)^{\kappa_\pi}L^{w^\circ}\operatorname{poly}(n, m).
--   $$
--   A feasible assignment can be recovered with polynomial overhead.
--
--   Precisely, for every valid instance $I$ (with $n$ events on $m$ qubits, cut rank $\kappa_\pi$ and frontier width $w^\circ$) and every positive integer $L$:
--
--   1. Algorithm 1 — its guards and its transition recursion — answers Yes if and only if $I$ is feasible in $L$ rounds;
--   2. there are a deterministic multitape machine and a constant $C$, fixed before the instance, which on input $\langle I, L\rangle$ ($L$ in binary) decide feasibility within $2^{C\kappa_\pi^2}(L+1)^{\kappa_\pi}L^{w^\circ+1}\cdot C(n+m+1)^C$ steps, visiting at most $2^{C\kappa_\pi^2}(L+1)^{\kappa_\pi}L^{w^\circ}\cdot C(n+m+1)^C$ cells beyond the input;
--   3. there are a machine, an output tape and a constant $C$ with the same bounds that also write a feasible layer assignment whenever one exists.
--
--   This is the paper's headline algorithmic bound (1): the exponential dependence is on the rank of the cross matrices of the anticommutation matrix and on the width of the residual-conflict frontier, not on the number of events.
--
--   Differences from the source:
--   - reading: the time and space of the DP of Algorithm 1 → a machine (clauses b and c) that decides feasibility, and writes a schedule, within the bounds; reason: Algorithm 1 is not itself a machine in Lean; clause (a) ties the decision to Algorithm 1, and the machine bound is the one an implementation of it achieves
--   - reading: 'time and space' with no machine model named → the published SubexponentialSAT deterministic multitape machine, with one machine and one constant C quantified before the instance; reason: a multitape bound implies the RAM bound; the constants of O(·) and poly do not depend on the instance
--   - reading: space S_cut → cells visited beyond the input length (visitedSpace ≤ σ + |input|); reason: the machine's space counts the input tape, and L is given in binary, so at κ_π = w° = 0 the printed bound cannot cover log L input cells
--   - reading: a feasible assignment can be recovered with polynomial overhead → a second machine within the same bound shapes (its own constant) that decides and writes a feasible assignment; reason: polynomial overhead is absorbed by C(n+m+1)^C
--   - encoding: 2^{O(κ_π²)} and poly(n, m) → 2^{Cκ_π²} and C(n+m+1)^C with one constant C; reason: the standard reading of O(·) and poly with a constant chosen before the instance
--   - reading: the DP of Algorithm 1 decides 3.2 exactly → Algorithm1Accepts (guards of lines 1–4 and the state recursion dpSet) iff Feasible, for every valid instance and every L ≥ 1; reason: this is the algorithm as printed; canonicalized states are compared as subspaces
--   - encoding: E_X on unordered pairs, signatures in F₂^{n−k} → Overlap on distinct pairs, zero-padded signatures in F₂^n; reason: same graphs, spans and kernels
--   - encoding: events 1..n and layers [L] = {1..L} → Fin n and Fin L (0-based; event i and layer t are the paper's i+1 and t+1); reason: index shift; same instances and assignments
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Theorem 5.2, p.10 (with Algorithm 1, p.10)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_CutRankSched_Instance
import Definitions.Def_CutRankSched_Instance_Valid
import Definitions.Def_CutRankSched_IsSchedule
import Definitions.Def_CutRankSched_Feasible
import Definitions.Def_CutRankSched_Algorithm1Accepts
import Definitions.Def_CutRankSched_encInput
import Definitions.Def_CutRankSched_encSchedule
import Definitions.Def_CutRankSched_timeBound
import Definitions.Def_CutRankSched_spaceBound
import Definitions.Def_CutRankSched_DecidesWithin
import Definitions.Def_CutRankSched_FindsWithin

set_option autoImplicit false

open OAI.Algorithms.SubexponentialSAT.Computation

namespace CutRankSched

/-- **Theorem 5.2 (Cut-rank scheduling DP)** (Zhao–Chen–Li–Kong–Peng–Yu–Yue, *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), Theorem 5.2, p.10). The DP of Algorithm 1
decides Problem 3.2 exactly. Its time and space are, respectively,
`T_cut = 2^{O(κ_π²)}(L+1)^{κ_π}L^{w°+1} poly(n, m)` and
`S_cut = 2^{O(κ_π²)}(L+1)^{κ_π}L^{w°} poly(n, m)`. A feasible assignment can be recovered by
recording predecessor pointers, with polynomial overhead.

Stated as three clauses, for every valid instance and every positive budget `L`:
(a) Algorithm 1 (its guards and its transition recursion `dpSet`) accepts iff the instance is
feasible; (b) one machine and one constant `C`, fixed before the instance, decide feasibility
within time `2^{Cκ_π²}(L+1)^{κ_π}L^{w°+1}·C(n+m+1)^C` and space
`2^{Cκ_π²}(L+1)^{κ_π}L^{w°}·C(n+m+1)^C` beyond the input; (c) one machine and constant do the same
and, on feasible instances, also write a feasible assignment.

**Formalization Note** Machine model: the published `SubexponentialSAT` `PrimitiveMachine`; input
`encInput I L` (`L` in binary); space counts visited cells beyond the input length. 0-based events
and layers. -/
theorem theorem_5_2 :
    (∀ (I : Instance) (L : ℕ), I.Valid → 1 ≤ L → (Algorithm1Accepts I L ↔ Feasible I L)) ∧
    (∃ (M : PrimitiveMachine) (C : ℕ), ∀ (I : Instance) (L : ℕ), I.Valid → 1 ≤ L →
      DecidesWithin M (encInput I L) (Feasible I L) (timeBound C I L) (spaceBound C I L)) ∧
    (∃ (M : PrimitiveMachine) (out : Fin M.tapeCount) (C : ℕ), ∀ (I : Instance) (L : ℕ),
      I.Valid → 1 ≤ L →
        FindsWithin M out (encInput I L) (Feasible I L)
          (fun w => ∃ lam : Fin I.n → Fin L, IsSchedule I L lam ∧ w = encSchedule lam)
          (timeBound C I L) (spaceBound C I L)) := by sorry

end CutRankSched
