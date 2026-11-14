-- Prove2me | Theorems.Thm_CatalyticTreeEval_Main_lemma_4_6
-- name    : CatalyticTreeEval.Main.lemma_4_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-11T16:31:38.394077+00:00
-- url     : https://prove2.me/theorems/6d1a22f0-39af-427a-993d-d7a4dd9a351c
-- title:
--   Lemma 4.6 — correctness of the actual one-level algorithm
-- statement:
--   Let a frame satisfy the section-four algebraic setting: positive label length, $m>1$, a noncancelling score set containing zero, an $S$-matching family, an $(S+S)$-decoder and the stated access-space scale bound. Let $W$ be any output vector family, $f$ any two-input label table, $x_0,x_1$ fixed hidden labels, $\alpha$ any scalar and $R$ any initial register state.
--
--   The explicitly defined Section 4.2 program, including the four-query inner-product prefix and every term and candidate-pair iteration, has the net effect
--
--   $$R\longmapsto R\text{ with position 2 replaced by }R_2+\alpha W_{f(x_0,x_1)}.$$
--
--   Both child registers remain unchanged at termination. Its child-operation list admits exact inverse pairs. No arbitrary transformation assumed to have this effect is substituted for the actual algorithm. This is its algebraic correctness assertion; charged implementation and resources are supplied by Theorem 4.4.
--
--   Differences from the source:
--   - encoding: finite binary labels, tuples and printing algorithms with O/poly resource notation → Fin indices, fixed self-delimiting binary encodings and charged finite-machine runs with positive uniform constants; reason: these encode the same objects; constants precede all varying construction parameters and all runs
--   - generalization: the uniform setting above the algorithm → the same algebraic setting without computational-access hypotheses; reason: only algebraic correctness is asserted here; the literal operation list is defined even without efficient printers, and Theorem 4.4 retains all access hypotheses
-- source:
--   Alexandra Henzinger, Edward Pyne, Seyoon Ragavan, Catalytic Tree Evaluation from Matching Vectors, STOC 2027 submission #533 (October 2026), Lemma 4.6, printed p. 24 (PDF p. 26); source.pdf SHA-256 17c3a71f0fb5afe2456558477e16fbac4200191e6e68f0facf212e24cb4ef238

import Definitions.Def_CatalyticTreeEval_Main_Framework

set_option autoImplicit false

namespace CatalyticTreeEval.Main

theorem lemma_4_6 (F : Frame) (hF : F.valid)
    (W : Label F.l → Vec F.m F.d) (f : Label F.l → Label F.l → Label F.l)
    (x : Fin 2 → Label F.l) (α : ZMod F.m) (R : Registers F.m F.d) :
    execute F.U F.V x R (oneLevelProgram F.U F.V W F.D f x α R) =
      addAt R 2 (α • W (f (x 0) (x 1))) ∧
    InversePairs (oneLevelProgram F.U F.V W F.D f x α R) := by sorry

end CatalyticTreeEval.Main
