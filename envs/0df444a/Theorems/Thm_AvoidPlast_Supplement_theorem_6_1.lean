-- Prove2me | Theorems.Thm_AvoidPlast_Supplement_theorem_6_1
-- name    : AvoidPlast.Supplement.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T16:50:41.943095+00:00
-- url     : https://prove2.me/theorems/baca280d-2fec-4309-a17c-e7b817879887
-- title:
--   Theorem 6.1 (= Theorem 1.5) — low-space Avoid is hard for NP in the worst case
-- statement:
--   If $\mathsf{NP}\ne\mathsf{PSPACE}$ then for every $\varepsilon>0$ there is a family
--   $$C=\bigl\{C_x:[4]\to\{0,1\}^{|x|^{\sqrt\varepsilon}}\bigr\}$$
--   evaluable in space $|x|^\varepsilon$ such that $\mathrm{Avoid}_C$ is not solvable in non-deterministic polynomial time in the worst case: every non-deterministic polynomial-time machine fails, on some input of infinitely many lengths, to have an accepting path all of whose outputs avoid the range of $C_x$.
--
--   Theorem 1.5 is the same statement after $\varepsilon\mapsto\varepsilon^2$.
--
--   Differences from the source:
--   - reading: "$\mathrm{Avoid}_C$ is not solvable in non-deterministic polynomial time (in the worst-case)" → no non-deterministic polynomial-time machine solves it on every input of every sufficiently large length; reason: for $\lceil n^{\sqrt\varepsilon}\rceil\le2$ the four values of $C_x$ may cover all outputs, so requiring every input would make the conclusion hold for a trivial reason
--   - encoding: $[4]$; $|x|^{\sqrt\varepsilon}$ → inputs of $2$ bits; $\lceil|x|^{\sqrt\varepsilon}\rceil$; reason: reading R3
--   - encoding: space $|x|^\varepsilon$ → $O(\cdot)$ with an explicit existential constant, $C\cdot(s(n)+1)$; reason: the mission's reading R2; the $+1$ covers $n=0$
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorem 6.1, p.31 (PDF p.33)

import Mathlib
import Definitions.Def_AvoidPlast_EvaluableInSpace
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_ceilPow
import Definitions.Def_AvoidPlast_Supplement_InPSPACE
import Definitions.Def_AvoidPlast_Supplement_InNP
import Definitions.Def_AvoidPlast_Supplement_IsPolyNTime
import Definitions.Def_AvoidPlast_Supplement_SolvesAvoidNDB

namespace AvoidPlast.Supplement

open AvoidPlast

/-- Theorem 6.1 (= Theorem 1.5 after `ε ↦ ε²`), low-space Avoid is hard in the worst case
(Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), p.31). If `NP ≠ PSPACE` then for every `ε > 0` there is a family
`C = {C_x : [4] → {0,1}^{|x|^{√ε}}}` evaluable in space `|x|^ε` such that `Avoid_C` is not solvable
in non-deterministic polynomial time: every non-deterministic polynomial-time machine fails to
solve `Avoid_C` on some input of infinitely many lengths.

**Formalization Note** `[4]` is `{0,1}^2`. "Solvable in the worst case" is: on every input of every
sufficiently large length, some witness is accepted and every accepted witness outputs a solution.
On short inputs (`⌈n^{√ε}⌉ ≤ 2`) the four values may cover the whole range, so "every input" would
make the conclusion hold for a trivial reason. -/
theorem theorem_6_1 (h : {L : Set (List Bool) | InNP L} ≠ {L | InPSPACE L}) :
    ∀ ε : ℝ, 0 < ε → ∃ C : List Bool → List Bool → List Bool,
      EvaluableInSpace C (fun _ => 2) (ceilPow (Real.sqrt ε)) (fun n => (n : ℝ) ^ ε) ∧
      ¬ ∃ (A : Machine 2) (a : ℕ), IsPolyNTime A a ∧ ∀ᶠ n : ℕ in Filter.atTop,
        ∀ x : List Bool, x.length = n →
          SolvesAvoidNDB A C (fun _ => 2) (ceilPow (Real.sqrt ε)) (fun n => a * (n ^ a + 1)) x := by sorry

end AvoidPlast.Supplement
