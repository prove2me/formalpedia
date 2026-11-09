-- Prove2me | Theorems.Thm_CEPolytopeHard_rubinstein_gcircuit_hard
-- name    : CEPolytopeHard.rubinstein_gcircuit_hard
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:18:07.633514+00:00
-- url     : https://prove2.me/theorems/9ce6d5aa-1d22-411f-a09d-440495a65c1b
-- title:
--   [71] (cited) — fan-out-two generalized circuits are PPAD-hard at a constant tolerance
-- statement:
--   There is a constant $\tau$ with $0 < \tau < 1/4$ such that the following problem is PPAD-hard: given a well-formed generalized circuit with fan-out two, compute a rational assignment in $[0,1]^d$ that satisfies **every** gate at tolerance $\tau$. In symbols,
--   $$
--   \exists\, \tau \in (0, 1/4):\quad \mathrm{GCircuit}(\tau, 0) \text{ is PPAD-hard}.
--   $$
--
--   The paper cites this result of Rubinstein [71] at the start of the proof of Theorem 4(i) ("It is known that satisfying a generalized circuit with fan-out two is PPAD-hard at some constant tolerance $0 < \tau < 1/4$"); it is the source problem of the reduction in clause (i).
--
--   Differences from the source:
--   - reading: generalized circuits with fan-out two as cited from [71] → the generalized circuits of Section 2.5 (constant, scaling, copying, addition, subtraction, comparison gates, β ∈ ℚ ∩ [0, 1]); reason: the sentence on p.20 refers to the paper's own Section 2.5 notion; footnote 4 notes that hardness holds with only truncated addition and complement gates
--   - encoding: satisfying the circuit; PPAD-hard → gcircuitProblem τ 0 (at least (1 − 0)d gates, rational assignments in [0, 1]^d); PPADHard over QuasiStrictNE.PPAD; reason: Lean representation of the search problem and of PPAD-hardness
-- source:
--   Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, The Complexity of Correlated Equilibria Beyond Normal-Form Games, arXiv:2605.17665 (held version of November 2, 2026, sha256 6aec500a…7820), proof of Theorem 4(i), "A polynomial map", p.20 (citing [71])

import Mathlib
import Definitions.Def_CEPolytopeHard_PPADHard
import Definitions.Def_CEPolytopeHard_gcircuitProblem

set_option autoImplicit false

namespace CEPolytopeHard

/-- **Generalized circuits with fan-out two are PPAD-hard at a constant tolerance** (Rubinstein
[71], cited in Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, *The Complexity of Correlated Equilibria Beyond Normal-Form Games*, arXiv:2605.17665, held version of November 2, 2026, sha256 6aec500a…7820, proof of Theorem 4(i), "A polynomial map", p.20: "It is known that
satisfying a generalized circuit with fan-out two is PPAD-hard at some constant tolerance
0 < τ < 1/4 [71]"). There is a constant `τ` with `0 < τ < 1/4` such that, given a well-formed
generalized circuit with fan-out two, computing a rational assignment in `[0, 1]^d` satisfying
every gate at tolerance `τ` is PPAD-hard.

**Formalization Note** "Satisfying" every gate is `gcircuitProblem τ 0` (at least `(1 − 0)d`
gates). Generalized circuits are the class of Section 2.5 (p.12): constant, scaling, copying,
addition, subtraction and comparison gates. The result is cited, not proved, in the paper. -/
theorem rubinstein_gcircuit_hard :
    ∃ τ : ℝ, 0 < τ ∧ τ < 1 / 4 ∧ PPADHard (gcircuitProblem τ 0) := by sorry

end CEPolytopeHard
