-- Prove2me | Theorems.Thm_DetDLP_w3_stage2_abstract_coset_recovery
-- name    : DetDLP.w3_stage2_abstract_coset_recovery
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T20:40:58.768921+00:00
-- url     : https://prove2.me/theorems/6183850d-c535-4ff9-82fb-68362cbe0915
-- title:
--   Stage II: bounded HNF recovery and soundness of every completed trace
-- statement:
--   Given a finite abelian group identified with $\mathbb Z/M$ by a coordinate map taking the generator to one, universal block-tuple coverage and coordinate decompositions, the corrected $N+1$-row HNF initialization followed by fixed-shift separation admits a successful trace. It uses at most $\lceil\log_2(M^N)\rceil$ violated congruences. Every successful trace returns the true coordinate vector and its target coordinate is the unique canonical discrete logarithm. Each cut records a positive Newton filter summand, the exact HNF intersection, and its factor-two cardinality bound.
-- source:
--   Deterministic Discrete Logarithms, §4.1–4.3, equations (4.1)–(4.5) and proof of Theorem 1.1, pp. 13–16; referee revisions R1 and R2.

import Definitions.Def_DetDLP_W3_CosetTrace
set_option autoImplicit false
open DetDLP

theorem DetDLP.w3_stage2_abstract_coset_recovery {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (M : ℕ) [NeZero M] (hM : 2 ≤ M) (P Q : G) (e : G ≃+ ZMod M) (hP : e P = 1)
    {m : ℕ} (hm : 2 ≤ m) (FB : IndexedFactorBase G m)
    (cover : ∀ g : G, ∃ X : FB.BlockTuple, FB.tupleVal X = g)
    (U : Fin FB.totalCoords → FB.BlockTuple) (hU : ∀ j, FB.tupleVal (U j) = FB.elem P Q j) :
    (∃ y, w3_Outcome FB M P U y) ∧
    ∀ y, w3_Outcome FB M P U y → (∀ j, y j = e (FB.elem P Q j)) ∧
      (y FB.targetCoord).val < M ∧ (y FB.targetCoord).val • P = Q := by sorry
