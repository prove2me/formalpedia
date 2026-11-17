-- Prove2me | Theorems.Thm_AvoidPlast_Supplement_theorem_6_9
-- name    : AvoidPlast.Supplement.theorem_6_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T16:53:15.113691+00:00
-- url     : https://prove2.me/theorems/9bc57d6d-5881-4348-8f1b-769798775ed0
-- title:
--   Theorem 6.9 (= Theorem 1.6) — an average-case non-deterministic algorithm for Avoid from one-way functions
-- statement:
--   If sub-exponentially secure one-way functions exist, then for some $\varepsilon>0$ there is a non-deterministic polynomial-time algorithm $A$ using only $n^\varepsilon$ non-deterministic bits such that for every family $C=\{C_x\}$ stretching $|x|^{\varepsilon^2}$ bits to $|x|^\varepsilon$ bits and evaluable in time $2^{|x|^{\varepsilon^2}}$, for infinitely many $n$,
--   $$\Pr_{x\in\{0,1\}^n}[A(x)\text{ solves }\mathrm{Avoid}(C_x)]\ge1/\mathrm{poly}(n),$$
--   where $A(x)$ solves $\mathrm{Avoid}(C_x)$ if on some witness it outputs an Avoid solution and on every witness an Avoid solution or $\bot$.
--
--   It indicates that Assumption 1.1 cannot be strengthened to non-deterministic algorithms that err.
--
--   Differences from the source:
--   - reading: "sub-exponentially secure one-way functions" (no definition in the paper) → Definition 6.10 without the permutation: polynomial-time $f$, $\rho\in(0,1)$, every inverter of time $2^{n^\rho}$ inverts $f(u)$ with negligible probability for large $n$; reason: this is the security the proofs of Theorems 6.9 and 7.11 contradict (an inverter of time $2^{n^\gamma}$ for every $\gamma>0$)
--   - encoding: $1/\mathrm{poly}(n)$ → $n^{-c}$ for a natural $c$ chosen after $C$; reason: the usual meaning
--   - generalization: "evaluable in time $2^{|x|^{\varepsilon^2}}$" → evaluable in time $O(\lceil2^{|x|^{\varepsilon^2}}\rceil)$; reason: more families are covered; the proof's inverter runs in time $2^{O(N^{\varepsilon^2})}$, which absorbs the constant
--   - encoding: lengths $n^a$ → $\lceil n^a\rceil$; reason: the mission's reading R3
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorem 6.9, p.37 (PDF p.39)

import Mathlib
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_ceilPow
import Definitions.Def_AvoidPlast_prob
import Definitions.Def_AvoidPlast_Supplement_IsPolyNTime
import Definitions.Def_AvoidPlast_Supplement_SolvesAvoidNDB
import Definitions.Def_AvoidPlast_Supplement_EvaluableInTime
import Definitions.Def_AvoidPlast_Supplement_expBound
import Definitions.Def_AvoidPlast_Supplement_SubexpOWF

namespace AvoidPlast.Supplement

open AvoidPlast

/-- Theorem 6.9 (= Theorem 1.6), an average-case non-deterministic algorithm (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), p.37). If
sub-exponentially secure one-way functions exist, then for some `ε > 0` there is a
non-deterministic polynomial-time `A` using only `n^ε` non-deterministic bits such that for every
family `C = {C_x}` stretching `|x|^{ε²}` bits to `|x|^ε` bits and evaluable in time `2^{|x|^{ε²}}`,
for infinitely many `n`, `Pr_{x∈{0,1}^n}[A(x) solves Avoid(C_x)] ≥ 1/poly(n)`: on some witness `A(x)`
outputs an Avoid solution, and on every witness a solution or `⊥`.

**Formalization Note** `1/poly(n)` is `n^{-c}` with `c` chosen after `C`. "Evaluable in time
`2^{|x|^{ε²}}`" is time `O(⌈2^{|x|^{ε²}}⌉)`. -/
theorem theorem_6_9 (h : SubexpOWF) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ (A : Machine 2) (a : ℕ), IsPolyNTime A a ∧
      ∀ C : List Bool → List Bool → List Bool,
        EvaluableInTime C (ceilPow (ε ^ 2)) (ceilPow ε) (expBound (ε ^ 2)) →
        ∃ c : ℕ, ∃ᶠ n : ℕ in Filter.atTop, (n : ℝ) ^ (-(c : ℝ)) ≤
          prob n (SolvesAvoidNDB A C (ceilPow (ε ^ 2)) (ceilPow ε) (ceilPow ε)) := by sorry

end AvoidPlast.Supplement
