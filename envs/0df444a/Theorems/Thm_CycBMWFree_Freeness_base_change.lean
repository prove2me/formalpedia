-- Prove2me | Theorems.Thm_CycBMWFree_Freeness_base_change
-- name    : CycBMWFree.Freeness.base_change
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:27:52.257702+00:00
-- url     : https://prove2.me/theorems/b6e114c4-041f-4314-bcb4-e84175a4a6a4
-- title:
--   §2.4, p. 11 — BMW base change
-- statement:
--   Let $P$ and $P'$ be degree-$r$ ground parameters on commutative rings $S$ and $S'$, and let $φ:S\to S'$ be a morphism of ground rings in the sense of Definition 2.13. For every $n$ there is an $S'$-algebra isomorphism
--   $$
--   S'\otimes_S W_{n,S,r}(P)\cong W_{n,S',r}(P').
--   $$
--   This identifies the algebra after changing its coefficient ring, including the sign-twisted cases of the morphism definition. **Formalization Note** The source writes $W\otimes_S S'$; the symmetric tensor order gives $S'\otimes_S W$ in Lean. The Kauffman-tangle counterpart is outside this mission.
-- source:
--   Goodman & Hauschild Mosley, Cyclotomic BMW algebras II, arXiv:math/0612065v5, p. 11, §2.4 following Definition 2.13

import Mathlib
import Definitions.Def_CycBMWFree_Freeness_Setting

noncomputable section
open scoped BigOperators

namespace CycBMWFree.Freeness
open QAlgorithms.Papers.Independent.Support21.P14

/-- Base change for the cyclotomic BMW algebra, §2.4, p. 11. -/
theorem base_change {S S' : Type*} [CommRing S] [CommRing S'] {r : ℕ}
    (P : GroundParameters S r) (P' : GroundParameters S' r) (φ : S →+* S')
    (hφ : IsGroundRingMorphism P P' φ) (n : ℕ) :
    letI := φ.toAlgebra
    Nonempty (TensorProduct S S' (BMW P n) ≃ₐ[S'] BMW P' n) := by sorry

end CycBMWFree.Freeness
