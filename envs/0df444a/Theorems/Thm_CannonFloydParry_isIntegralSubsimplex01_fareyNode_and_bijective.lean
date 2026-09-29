-- Prove2me | Theorems.Thm_CannonFloydParry_isIntegralSubsimplex01_fareyNode_and_bijective
-- name    : CannonFloydParry.isIntegralSubsimplex01_fareyNode_and_bijective
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-26T20:08:37.245259+00:00
-- url     : https://prove2.me/theorems/adf64787-d269-4eec-ac7b-4f8aace93569
-- title:
--   p. 252 — the tree 𝒯′ of integral subsimplices is an ordered rooted binary tree
-- statement:
--   Following a finite word of left and right steps from $[0,1]$, taking left and right parts (`fareyNode`), gives an integral subsimplex of $[0,1]$; distinct words give distinct intervals; and every integral subsimplex of $[0,1]$ is reached by some word.
--
--   **Formalization Note.** "$\mathcal{T}'$ is an ordered rooted binary tree" is stated as this bijection between finite binary words, the vertices of the full ordered rooted binary tree, and the integral subsimplices of $[0,1]$, the child relation being left and right part.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathématique (2) 42 (1996) 215–256, https://doi.org/10.5169/seals-87877, section 7, p. 252, the tree 𝒯′

import Mathlib
import Definitions.Def_CannonFloydParry_PIP

namespace CannonFloydParry

theorem isIntegralSubsimplex01_fareyNode_and_bijective :
    (∀ w, IsIntegralSubsimplex01 (fareyNode w).lo (fareyNode w).hi) ∧
      Function.Injective (fun w => ((fareyNode w).lo, (fareyNode w).hi)) ∧
      ∀ p q, IsIntegralSubsimplex01 p q → ∃ w, (fareyNode w).lo = p ∧ (fareyNode w).hi = q := by
  sorry

end CannonFloydParry
