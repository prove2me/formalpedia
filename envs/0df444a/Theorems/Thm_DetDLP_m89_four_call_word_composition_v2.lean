-- Prove2me | Theorems.Thm_DetDLP_m89_four_call_word_composition_v2
-- name    : DetDLP.m89_four_call_word_composition_v2
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T18:26:09.117627+00:00
-- url     : https://prove2.me/theorems/bf4500da-d924-4e7e-87ae-daa87d1c443d
-- title:
--   Bounded composition of four word-processing machines
-- statement:
--   Let $p\ge2$ and suppose the common input word $x$ has length at most $\operatorname{bitLen}(p)+2$. Two bounded producers receive $x$, a converter receives the second producer’s output, and a final machine receives the framed triple consisting of $x$ and both required intermediate words. The result is computable by one multitape machine within a Stage I time and space bound at a fixed larger scale.
-- source:
--   S. Liu, B. Zhang and K. Ren, A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem, Zhejiang University preprint, 23 November 2026, Proposition 3.3 and its proof, Section 3.3.

import Definitions.Def_DetDLP_Machine

open DetDLP OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation

theorem DetDLP.m89_four_call_word_composition_v2
    (A : PrimitiveMachine) (oa : Fin A.tapeCount) (B : PrimitiveMachine) (ob : Fin B.tapeCount)
    (D : PrimitiveMachine) (od : Fin D.tapeCount) (E : PrimitiveMachine) (oe : Fin E.tapeCount)
    (k : ℕ) : ∃ (M : PrimitiveMachine) (o : Fin M.tapeCount) (c : ℕ),
      ∀ (p : ℕ), 2 ≤ p → ∀ (x a b d e : List Bool), x.length ≤ bitLen p + 2 →
        let W := mainSpaceBound k (bitLen p)
        let pack := Encoding.encodeList id [x,a,d]
        RunsWithin A oa x a (W+1) (W+1) → RunsWithin B ob x b (W+1) (W+1) →
        RunsWithin D od b d ((W+1)*(b.length+1)) ((W+1)*(b.length+1)) →
        RunsWithin E oe pack e ((W+1)*(pack.length+1)) ((W+1)*(pack.length+1)) →
        RunsWithin M o x e (mainSpaceBound c (bitLen p)) (mainSpaceBound c (bitLen p)) := by sorry
