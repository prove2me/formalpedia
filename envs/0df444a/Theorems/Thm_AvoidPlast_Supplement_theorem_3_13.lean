-- Prove2me | Theorems.Thm_AvoidPlast_Supplement_theorem_3_13
-- name    : AvoidPlast.Supplement.theorem_3_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T16:43:11.824482+00:00
-- url     : https://prove2.me/theorems/3f0f19e7-bab6-4fc8-ba8b-2352959dc560
-- title:
--   Theorem 3.13 — space hierarchy on all inputs
-- statement:
--   For all reals $0<c<C$ there is a language $L\in\mathrm{SPACE}[n^C]$ that is hard for $\mathrm{SPACE}[n^c]$ infinitely often on all inputs: for every machine $M$ of space $n^c$ there are infinitely many $n$ such that
--   $$M(x)\ne L(x)\quad\text{for all }x\in\{0,1\}^n.$$
--
--   It is the hierarchy theorem behind Theorem 3.14, which turns the paper's average-case conclusions into $\mathsf P\ne\mathsf{PSPACE}$.
--
--   Differences from the source:
--   - reading: "for every $C>c$" → $0<c<C$; reason: "$n^c$-space machine" with $c>0$, as in Theorem 3.14 where it is applied
--   - encoding: space $n^c$, $\mathrm{SPACE}[n^C]$ → $O(\cdot)$ with an explicit existential constant, $C\cdot(s(n)+1)$; reason: the mission's reading R2; the $+1$ covers $n=0$
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorem 3.13, p.16 (PDF p.18)

import Mathlib
import Definitions.Def_AvoidPlast_Accepts
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_SpaceO
import Definitions.Def_AvoidPlast_Supplement_InSPACE

namespace AvoidPlast.Supplement

open AvoidPlast

/-- Theorem 3.13, a space hierarchy on all inputs (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), p.16). For all reals `0 < c < C` there
is `L ∈ SPACE[n^C]` such that for every machine `M` of space `n^c` there are infinitely many `n`
with `M(x) ≠ L(x)` for **every** `x ∈ {0,1}^n`.

**Formalization Note** Space `n^c` is `O(n^c)` with halting on every input (`SpaceO`, reading R2);
`M(x) ≠ L(x)` is that acceptance of `x` differs from membership. -/
theorem theorem_3_13 : ∀ c C : ℝ, 0 < c → c < C → ∃ L : Set (List Bool),
    InSPACE (fun n => (n : ℝ) ^ C) L ∧ ∀ M : Machine 1, SpaceO M (fun n => (n : ℝ) ^ c) →
      ∃ᶠ n : ℕ in Filter.atTop, ∀ x : List Bool, x.length = n →
        ¬ (Accepts M ![x] ↔ x ∈ L) := by sorry

end AvoidPlast.Supplement
