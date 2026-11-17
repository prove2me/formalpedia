-- Prove2me | Theorems.Thm_AvoidPlast_Supplement_theorem_3_14
-- name    : AvoidPlast.Supplement.theorem_3_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T16:43:47.716986+00:00
-- url     : https://prove2.me/theorems/7a957852-1c78-4879-b49f-14c9c8bec90c
-- title:
--   Theorem 3.14 — the average-case conclusions imply $\mathsf P\ne\mathsf{PSPACE}$
-- statement:
--   Assume that for some fixed $c>0$, every $L\in\mathsf P$ has a machine $M_L$ of space $n^c$ such that for every $n\in\mathbb N$ there is $x\in\{0,1\}^n$ with $M_L(x)=L(x)$. Then $\mathsf P\ne\mathsf{PSPACE}$.
--
--   The hypothesis is much weaker than the average-case simulations of Theorems 5.8 and 5.14, so those conclusions would separate $\mathsf P$ from $\mathsf{PSPACE}$.
--
--   Differences from the source:
--   - encoding: space $n^c$ → $O(\cdot)$ with an explicit existential constant, $C\cdot(s(n)+1)$; reason: the mission's reading R2; the $+1$ covers $n=0$
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorem 3.14, p.16 (PDF p.18)

import Mathlib
import Definitions.Def_AvoidPlast_Accepts
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_SpaceO
import Definitions.Def_AvoidPlast_Supplement_InP
import Definitions.Def_AvoidPlast_Supplement_InPSPACE

namespace AvoidPlast.Supplement

open AvoidPlast

/-- Theorem 3.14 (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), p.16). If for some fixed `c > 0` every `L ∈ P` has a machine `M_L` of
space `n^c` that, for every `n`, agrees with `L` on at least one `x ∈ {0,1}^n`, then `P ≠ PSPACE`. -/
theorem theorem_3_14 (h : ∃ c : ℝ, 0 < c ∧ ∀ L : Set (List Bool), InP L → ∃ M : Machine 1,
      SpaceO M (fun n => (n : ℝ) ^ c) ∧
      ∀ n : ℕ, ∃ x : List Bool, x.length = n ∧ (Accepts M ![x] ↔ x ∈ L)) :
    {L : Set (List Bool) | InP L} ≠ {L | InPSPACE L} := by sorry

end AvoidPlast.Supplement
