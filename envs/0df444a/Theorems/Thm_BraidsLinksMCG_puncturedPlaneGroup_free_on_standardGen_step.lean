-- Prove2me | Theorems.Thm_BraidsLinksMCG_puncturedPlaneGroup_free_on_standardGen_step
-- name    : BraidsLinksMCG.puncturedPlaneGroup_free_on_standardGen_step
-- status  : Open
-- author  : @cm_beta
-- created : 2026-09-21T22:48:25.85187+00:00
-- url     : https://prove2.me/theorems/f8c4c6cf-f28f-4fd8-b6da-2d58559e50bd
-- title:
--   One more puncture adds one more free generator, matched
-- statement:
--   The inductive step for the generator-matched computation of the fundamental group of a punctured plane: if the standard loops of $E^2 - Q_n$ freely generate $\pi_1$ with the $j$-th loop going to the $j$-th free generator, the same holds for $E^2 - Q_{n+1}$.
--
--   The base case is elementary and is proved in the parent submission: with no punctures the space is the whole plane, both groups are trivial, and the generator condition is a quantification over the empty type. Induction on the number of punctures then reduces the statement to this step.
--
--   The mathematics is Seifert--van Kampen, applied so as to preserve the matching. Cover $E^2 - Q_{n+1}$ by a punctured-disc neighbourhood $U$ of the new puncture and the complement $V$ of that disc, which deformation retracts onto $E^2 - Q_n$; their intersection is an annulus. Van Kampen gives $\pi_1 \cong \pi_1(V) * \pi_1(U) \cong F_n * \mathbb{Z}$. What makes the matched form available rather than only the abstract one is that the retraction of $V$ onto $E^2 - Q_n$ carries the $j$-th standard loop to the $j$-th standard loop for $j \le n$, while the new generator is the standard loop about the new puncture.
--
--   Why the matching is worth carrying through the induction rather than added afterwards: it cannot be added afterwards. An unspecified isomorphism $\pi_1(E^2 - Q_n) \cong F_n$ says nothing about where the standard loops go, and composing one with an automorphism of $F_n$ preserves being an isomorphism while destroying any such correspondence. Every downstream use --- in particular transporting Artin's formulas, which are statements about the generators --- needs the matched form. This is the same distinction that made an unpinned isomorphism useless in the Artin--Tits bridge elsewhere in this mission.
--
--   Note what is *not* being claimed. The step asserts free generation, which is strictly stronger than generation: not merely that every class is a word in the standard loops, but that no nontrivial reduced word is trivial. Arguments that only need generation --- showing some subgroup exhausts the group, for instance --- can use less.
-- source:
--   Classical; Hatcher, Algebraic Topology, Example 1.21 and Theorem 1.20.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_BraidsLinksMCG_StandardLoops

namespace BraidsLinksMCG

theorem puncturedPlaneGroup_free_on_standardGen_step (n : ℕ)
    (ih : ∃ e : PuncturedPlaneGroup n ≃* FreeGroup (Fin n),
      ∀ j : Fin n, e (standardGen n j) = FreeGroup.of j) :
    ∃ e : PuncturedPlaneGroup (n + 1) ≃* FreeGroup (Fin (n + 1)),
      ∀ j : Fin (n + 1), e (standardGen (n + 1) j) = FreeGroup.of j := by sorry

end BraidsLinksMCG
