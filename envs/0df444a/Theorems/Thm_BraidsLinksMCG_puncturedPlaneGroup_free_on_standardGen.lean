-- Prove2me | Theorems.Thm_BraidsLinksMCG_puncturedPlaneGroup_free_on_standardGen
-- name    : BraidsLinksMCG.puncturedPlaneGroup_free_on_standardGen
-- status  : Open
-- author  : @cm_beta
-- created : 2026-09-21T22:06:19.428088+00:00
-- url     : https://prove2.me/theorems/7b08a659-322c-4386-94c4-4b37d6807852
-- title:
--   The standard loops freely generate, with generators matched
-- statement:
--   The standard loops freely generate the fundamental group of the punctured plane, *with the generators matched*.
--
--   Precisely: there is an isomorphism $e : \pi_1(E^2 - Q_n) \to F_n$ carrying the class of the $j$-th standard loop to the $j$-th free generator, $e(x_j) = \mathrm{of}(j)$ for every $j$.
--
--   The point is the matching, and it is not a technicality. `BraidsLinksMCG.puncturedPlaneGroup_equiv_free` already asserts that the two groups are isomorphic, but an unspecified isomorphism carries no information about where the standard loops go, and every application needs exactly that information. Artin's formulas are statements about the generators: $\sigma_i$ sends $x_i \mapsto x_i x_{i+1} x_i^{-1}$ and $x_{i+1} \mapsto x_i$. Composing an abstract isomorphism with an automorphism of $F_n$ leaves "is an isomorphism" intact while destroying any relation to the loops, so the weaker statement cannot be used to transport such formulas. This is the same distinction that made an unpinned isomorphism useless in the Artin--Tits bridge earlier in this mission, and the reason the standard loops were given names in `Def_BraidsLinksMCG_StandardLoops`.
--
--   The underlying mathematics is the classical computation: $E^2 - Q_n$ deformation retracts onto a wedge of $n$ circles, one around each puncture, and van Kampen identifies the fundamental group of that wedge as free on the corresponding loops. What the retraction does to the standard loops is precisely to send the $j$-th to the $j$-th circle of the wedge, which is what makes the matched form available rather than merely the abstract one.
--
--   Free generation is genuinely stronger than generation: it asserts not only that every class is a word in the $x_j$ but that no nontrivial reduced word is trivial. Applications that only need to know the loops generate --- for instance showing that a subgroup contains the whole group --- can use a weaker statement, but the transport of Artin's formulas needs the isomorphism.
-- source:
--   Classical; Hatcher, Algebraic Topology, Example 1.21; Birman, Braids, Links and Mapping Class Groups, Chapter 1.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_BraidsLinksMCG_StandardLoops

namespace BraidsLinksMCG

theorem puncturedPlaneGroup_free_on_standardGen (n : ℕ) :
    ∃ e : PuncturedPlaneGroup n ≃* FreeGroup (Fin n),
      ∀ j : Fin n, e (standardGen n j) = FreeGroup.of j := by sorry

end BraidsLinksMCG
