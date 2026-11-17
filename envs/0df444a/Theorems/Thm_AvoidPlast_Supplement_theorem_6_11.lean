-- Prove2me | Theorems.Thm_AvoidPlast_Supplement_theorem_6_11
-- name    : AvoidPlast.Supplement.theorem_6_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T16:54:06.874022+00:00
-- url     : https://prove2.me/theorems/8638c5dd-ad53-49be-84ec-27bf77cf7b48
-- title:
--   Theorem 6.11 — a high-success non-deterministic algorithm for Avoid from one-way permutations
-- statement:
--   If sub-exponentially secure strong one-way permutations exist (Definition 6.10), then for some $\varepsilon>0$ there is a non-deterministic polynomial-time algorithm $A$ using only $n^\varepsilon$ non-deterministic bits such that for every family $C$ stretching $|x|^{\varepsilon^2}$ bits to $|x|^\varepsilon$ bits and evaluable in time $2^{|x|^{\varepsilon^2}}$, for infinitely many $n$,
--   $$\Pr_{x\in\{0,1\}^n}[A(x)\text{ solves }\mathrm{Avoid}(C_x)]\ge1-n^{-\omega(1)},$$
--   in the sense of Theorem 6.9.
--
--   Differences from the source:
--   - encoding: $n^{-\omega(1)}$ → a negligible $\nu$ chosen after $C$; reason: the mission's reading R1
--   - encoding: $I(1^n,u)=f^{-1}(u)$ (Definition 6.10) → $f(I(1^n,u))=u$; reason: the same event, since $f$ is a permutation
--   - generalization: "evaluable in time $2^{|x|^{\varepsilon^2}}$" → evaluable in time $O(\lceil2^{|x|^{\varepsilon^2}}\rceil)$; reason: more families are covered; the proof's inverter runs in time $2^{O(N^{\varepsilon^2})}$, which absorbs the constant
--   - encoding: lengths $n^a$ → $\lceil n^a\rceil$; reason: the mission's reading R3
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorem 6.11, p.38 (PDF p.40)

import Mathlib
import Definitions.Def_QuantumPRC_Negligible
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_ceilPow
import Definitions.Def_AvoidPlast_prob
import Definitions.Def_AvoidPlast_Supplement_IsPolyNTime
import Definitions.Def_AvoidPlast_Supplement_SolvesAvoidNDB
import Definitions.Def_AvoidPlast_Supplement_EvaluableInTime
import Definitions.Def_AvoidPlast_Supplement_expBound
import Definitions.Def_AvoidPlast_Supplement_SubexpStrongOWP

namespace AvoidPlast.Supplement

open AvoidPlast

/-- Theorem 6.11, a high-success non-deterministic algorithm from one-way permutations (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728),
p.38). If sub-exponentially secure strong one-way permutations exist (Definition 6.10), then for
some `ε > 0` there is a non-deterministic polynomial-time `A` using only `n^ε` non-deterministic bits
such that for every family `C` stretching `|x|^{ε²}` bits to `|x|^ε` bits and evaluable in time
`2^{|x|^{ε²}}`, for infinitely many `n`, `Pr_{x∈{0,1}^n}[A(x) solves Avoid(C_x)] ≥ 1 - n^{-ω(1)}` (in
the sense of Theorem 6.9).

**Formalization Note** `n^{-ω(1)}` is a negligible `ν` chosen after `C` (reading R1). -/
theorem theorem_6_11 (h : SubexpStrongOWP) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ (A : Machine 2) (a : ℕ), IsPolyNTime A a ∧
      ∀ C : List Bool → List Bool → List Bool,
        EvaluableInTime C (ceilPow (ε ^ 2)) (ceilPow ε) (expBound (ε ^ 2)) →
        ∃ ν : ℕ → ℝ, QuantumPRC.Negligible ν ∧ ∃ᶠ n : ℕ in Filter.atTop, 1 - ν n ≤
          prob n (SolvesAvoidNDB A C (ceilPow (ε ^ 2)) (ceilPow ε) (ceilPow ε)) := by sorry

end AvoidPlast.Supplement
