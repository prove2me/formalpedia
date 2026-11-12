-- Prove2me | Theorems.Thm_CatalyticTreeEval_Main_lemma_4_5
-- name    : CatalyticTreeEval.Main.lemma_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T16:30:31.82114+00:00
-- url     : https://prove2.me/theorems/fc911884-3836-4221-a353-a3ad79258530
-- title:
--   Lemma 4.5 — four-query masked inner product
-- statement:
--   Let $m>1$, $d>0$, and let $U,V$ be arbitrary vector families indexed by labels of any nonnegative bitlength. For two fixed hidden labels and arbitrary starting registers $R_0,R_1,R_2$, the literal swap-and-query procedure computes locally
--
--   $$g=\langle R_0,V_{x_0}\rangle+\langle R_1,V_{x_1}\rangle.$$
--
--   A single finite oracle machine realizes the procedure using exactly four queries, at most $C(1+\log_2d+\log_2m)$ local work bits, and at most $C\log_2m$ retained bits at a query. It halts with all three registers restored and the scalar in local work. Each child operation is paired with its exact inverse, including the two swaps. The hidden labels are accessible only through the positional oracle.
--
--   This is the masked scalar needed in the one-level algorithm. The resource statement and scalar equality refer to the same concrete procedure.
--
--   Differences from the source:
--   - encoding: finite binary labels, tuples and printing algorithms with O/poly resource notation → Fin indices, fixed self-delimiting binary encodings and charged finite-machine runs with positive uniform constants; reason: these encode the same objects; constants precede all varying construction parameters and all runs
--   - generalization: the setting of Theorem 4.4, including matching, decoding and uniform-access conditions → arbitrary U,V, nonnegative label length and only m>1,d>0; reason: the swap procedure reads register contents and uses the oracle, never the matching, decoder or access hypotheses; every source instance specializes to this statement
-- source:
--   Alexandra Henzinger, Edward Pyne, Seyoon Ragavan, Catalytic Tree Evaluation from Matching Vectors, STOC 2027 submission #533 (October 2026), Lemma 4.5, printed p. 23 (PDF p. 25); source.pdf SHA-256 17c3a71f0fb5afe2456558477e16fbac4200191e6e68f0facf212e24cb4ef238

import Definitions.Def_CatalyticTreeEval_Main_OracleMachine

set_option autoImplicit false

namespace CatalyticTreeEval.Main

/-- The masked inner-product procedure needs no matching or decoding property. -/
theorem lemma_4_5 :
    ∃ (P : OracleMachine) (C : ℝ), 0 < C ∧
      ∀ (m d l : ℕ), 1 < m → 0 < d →
      ∀ (U V : Label l → Vec m d) (x : Fin 2 → Label l) (R : Registers m d),
      let ip := innerProgram U V x R
      ip.1 = (R 0 ⬝ᵥ V (x 0)) + (R 1 ⬝ᵥ V (x 1)) ∧
      execute U V x R ip.2 = R ∧ InversePairs ip.2 ∧
      (ip.2.filter (fun op => match op with | .query _ _ _ => true | _ => false)).length = 4 ∧
      OracleExecution P U V x (natsCode [m,d]) 0 R ip.2
        (C * (1 + log₂ d + log₂ m)) (C * log₂ m) none (some ip.1) := by sorry

end CatalyticTreeEval.Main
