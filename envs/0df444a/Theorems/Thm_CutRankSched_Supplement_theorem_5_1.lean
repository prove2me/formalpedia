-- Prove2me | Theorems.Thm_CutRankSched_Supplement_theorem_5_1
-- name    : CutRankSched.Supplement.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:52:59.336952+00:00
-- url     : https://prove2.me/theorems/b8e7bbf8-c949-4642-b0e7-2419bcc9c947
-- title:
--   Theorem 5.1 — global-rank scheduling DP
-- statement:
--   For every valid instance and every positive budget $L$:
--
--   1. for **every** rank factorization $A=BC$ over $\mathbb F_2$ with $B\in\mathbb F_2^{n\times r}$, $C\in\mathbb F_2^{r\times n}$ and $r=\mathrm{rank}_{\mathbb F_2}A$, the global-rank DP (flags (6), tests (7) and (5), update (8)) accepts if and only if the instance is feasible in $L$ rounds;
--   2. there are one machine and one constant $C$, fixed before the instance, that decide feasibility within time and space beyond the input
--   $$
--   2^{Cr^2}(L+1)^rL^{w^\circ+1}\cdot C(n+m+1)^C \quad\text{and}\quad 2^{Cr^2}(L+1)^rL^{w^\circ}\cdot C(n+m+1)^C ,
--   $$
--   i.e. time $2^{O(r^2)}(L+1)^rL^{w^\circ+1}\,\mathrm{poly}(n,m)$ and space $2^{O(r^2)}(L+1)^rL^{w^\circ}\,\mathrm{poly}(n,m)$.
--
--   This is the global-rank predecessor of the cut-rank algorithm of Theorem 5.2, with the global rank $r\le 2m$ in place of the cut rank $\kappa_\pi\le r$.
--
--   **Formalization Note** Same machine model and input encoding as the base goal `CutRankSched.theorem_5_2`.
--
--   Differences from the source:
--   - reading: the above DP accepts exactly the feasible instances → for every rank factorization A = BC with r = rank A, the state set after event n is nonempty iff Feasible I L; reason: the DP depends on the chosen factorization; the source's proof works for any; the Section 5.1 preprocessing shortcuts (n = 0, L ≥ n, n > mL) are not part of the DP's acceptance
--   - reading: 2^{O(·)} and poly(n, m) running time (and space) of an algorithm → one PrimitiveMachine (the published SubexponentialSAT model) and one constant C, both fixed before the instance, on input encInput I L (L in binary); space counts visited cells beyond the input; reason: the paper names no machine model; this is the reading of the published base goal CutRankSched.theorem_5_2
--   - encoding: events 1..n and layers [L] = {1..L} → Fin n and Fin L (0-based); reason: index shift; same instances and assignments
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Theorem 5.1, p.9

import Mathlib
import Definitions.Def_CutRankSched_Instance
import Definitions.Def_CutRankSched_Instance_Valid
import Definitions.Def_CutRankSched_A
import Definitions.Def_CutRankSched_Feasible
import Definitions.Def_CutRankSched_encInput
import Definitions.Def_CutRankSched_DecidesWithin
import Definitions.Def_CutRankSched_Supplement_GlobalDPAccepts
import Definitions.Def_CutRankSched_Supplement_gTimeBound
import Definitions.Def_CutRankSched_Supplement_gSpaceBound

set_option autoImplicit false

open OAI.Algorithms.SubexponentialSAT.Computation

namespace CutRankSched

namespace Supplement

/-- **Theorem 5.1 (Global-rank scheduling DP)** (Zhao et al., *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), Theorem 5.1, p.9). The DP of §5.2 accepts
exactly the feasible instances of Problem 3.2. It runs in time `2^{O(r²)}(L+1)^r L^{w°+1} poly(n, m)`
and uses space `2^{O(r²)}(L+1)^r L^{w°} poly(n, m)`.

Stated as two clauses, for every valid instance and every positive budget `L`:
(a) for **every** rank factorization `A = BC` over `𝔽₂` (`B ∈ 𝔽₂^{n×r}`, `C ∈ 𝔽₂^{r×n}`,
`r = rank A`), the DP (flags (6), tests (7) and (5), update (8)) accepts iff the instance is
feasible; (b) one machine and one constant `C`, fixed before the instance, decide feasibility
within time `2^{Cr²}(L+1)^r L^{w°+1}·C(n+m+1)^C` and space `2^{Cr²}(L+1)^r L^{w°}·C(n+m+1)^C` beyond
the input.

**Formalization Note** Machine model, input encoding (`L` in binary) and space convention as in the
base goal `CutRankSched.theorem_5_2`. 0-based events and layers. -/
theorem theorem_5_1 :
    (∀ (I : Instance) (L : ℕ), I.Valid → 1 ≤ L →
      ∀ (r : ℕ) (B : Matrix (Fin I.n) (Fin r) (ZMod 2)) (C : Matrix (Fin r) (Fin I.n) (ZMod 2)),
        A I = B * C → r = (A I).rank → (GlobalDPAccepts I L B C ↔ Feasible I L)) ∧
    (∃ (M : PrimitiveMachine) (C : ℕ), ∀ (I : Instance) (L : ℕ), I.Valid → 1 ≤ L →
      DecidesWithin M (encInput I L) (Feasible I L) (gTimeBound C I L) (gSpaceBound C I L)) := by sorry

end Supplement

end CutRankSched
