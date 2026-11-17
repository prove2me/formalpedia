-- Prove2me | Theorems.Thm_CutRankSched_Supplement_theorem_6_4_algorithm
-- name    : CutRankSched.Supplement.theorem_6_4_algorithm
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:54:48.321346+00:00
-- url     : https://prove2.me/theorems/9a38e38f-779f-4407-98e4-936d686c40ff
-- title:
--   Theorem 6.4 (second sentence) — an $L^{mL}\,\mathrm{poly}(n,m)$ decision algorithm
-- statement:
--   There are one machine and one constant $C$, fixed before the instance, such that for every valid instance and every positive budget $L$ the machine decides whether the instance is feasible in $L$ rounds within
--   $$
--   L^{mL}\cdot C(n+m+1)^C
--   $$
--   steps: an elementary $L^{mL}\,\mathrm{poly}(n,m)$ algorithm parameterized by $(m,L)$.
--
--   This is the trivial-enumeration baseline that any parameterized algorithm for the problem has to beat. The first sentence of Theorem 6.4, $n\le mL$ for feasible instances (Eq. (15)), is the base milestone `CutRankSched.theorem_6_4_eq_15`.
--
--   Differences from the source:
--   - reading: an elementary L^{mL} poly(n, m) algorithm → one PrimitiveMachine (the published SubexponentialSAT model) and one constant C, both fixed before the instance, deciding Feasible I L on input encInput I L (L in binary) within L^{mL}·C(n+m+1)^C steps (DecidesInTime, no space clause); reason: the paper names no machine model and states time only; this is the machine reading of the published base goal CutRankSched.theorem_5_2
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Theorem 6.4, p.13

import Mathlib
import Definitions.Def_CutRankSched_Instance
import Definitions.Def_CutRankSched_Instance_Valid
import Definitions.Def_CutRankSched_Feasible
import Definitions.Def_CutRankSched_encInput
import Definitions.Def_CutRankSched_Supplement_DecidesInTime

set_option autoImplicit false

open OAI.Algorithms.SubexponentialSAT.Computation

namespace CutRankSched

namespace Supplement

/-- **Theorem 6.4, second sentence (trivial enumeration)** (Zhao et al., *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), Theorem 6.4, p.13).
Consequently the decision problem has an elementary `L^{mL} poly(n, m)` algorithm parameterized by
`(m, L)`.

Stated as: one machine and one constant `C`, fixed before the instance, decide feasibility of every
valid instance with every positive budget `L` within `L^{mL}·C(n+m+1)^C` steps.

**Formalization Note** Machine model and input `encInput I L` (`L` in binary) as in the base goal;
time only, as the theorem states no space bound. The first sentence, Eq. (15), is the published
`CutRankSched.theorem_6_4_eq_15`. -/
theorem theorem_6_4_algorithm :
    ∃ (M : PrimitiveMachine) (C : ℕ), ∀ (I : Instance) (L : ℕ), I.Valid → 1 ≤ L →
      DecidesInTime M (encInput I L) (Feasible I L)
        (L ^ (I.m * L) * (C * (I.n + I.m + 1) ^ C)) := by sorry

end Supplement

end CutRankSched
