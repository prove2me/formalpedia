-- Prove2me | Theorems.Thm_AvoidPlast_Supplement_theorem_5_10
-- name    : AvoidPlast.Supplement.theorem_5_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T16:49:03.58221+00:00
-- url     : https://prove2.me/theorems/fa96a916-9ed9-4613-b4e5-38ad994c90b6
-- title:
--   Theorem 5.10 — worst-case simulation of E in low space
-- statement:
--   Assume that for every $L\in\mathsf P$ and every $\varepsilon>0$ there is an algorithm $A$ of space $n^\varepsilon$ such that $\Pr_{x\in\{0,1\}^n}[A(x)=L(x)]\ge.999$ for all $n\in\mathbb N$. Then
--   $$\mathsf E\subseteq\bigcap_{\varepsilon>0}\mathrm{SPACE}[2^{\varepsilon n}].$$
--
--   Differences from the source:
--   - encoding: space $n^\varepsilon$, $\mathrm{SPACE}[2^{\varepsilon n}]$ → $O(\cdot)$ with an explicit existential constant, $C\cdot(s(n)+1)$; reason: the mission's reading R2; the $+1$ covers $n=0$
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorem 5.10, p.26 (PDF p.28)

import Mathlib
import Definitions.Def_AvoidPlast_Accepts
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_SpaceO
import Definitions.Def_AvoidPlast_prob
import Definitions.Def_AvoidPlast_Supplement_InP
import Definitions.Def_AvoidPlast_Supplement_InE
import Definitions.Def_AvoidPlast_Supplement_InSPACE

namespace AvoidPlast.Supplement

open AvoidPlast

/-- Theorem 5.10, worst-case simulation of E in low space (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), p.26). If for every `L ∈ P` and
every `ε > 0` some machine `A` of space `n^ε` has `Pr_{x∈{0,1}^n}[A(x) = L(x)] ≥ .999` for all `n`,
then `E ⊆ ∩_{ε>0} SPACE[2^{εn}]`. -/
theorem theorem_5_10
    (h : ∀ L : Set (List Bool), InP L → ∀ ε : ℝ, 0 < ε → ∃ A : Machine 1,
      SpaceO A (fun n => (n : ℝ) ^ ε) ∧
      ∀ n : ℕ, (0.999 : ℝ) ≤ prob n (fun x => Accepts A ![x] ↔ x ∈ L)) :
    ∀ L : Set (List Bool), InE L → ∀ ε : ℝ, 0 < ε → InSPACE (fun n => (2 : ℝ) ^ (ε * n)) L := by sorry

end AvoidPlast.Supplement
