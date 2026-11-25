-- Prove2me | Theorems.Thm_DetDLP_m89_four_call_word_composition
-- name    : DetDLP.m89_four_call_word_composition
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T17:54:57.451795+00:00
-- url     : https://prove2.me/theorems/6f6b7f46-18d2-4512-8b13-122ac8348fe5
-- title:
--   Bounded composition of two word producers, a converter, and a consumer
-- statement:
--   Let $W$ denote the Stage I budget at the specified scale $k$ and prime-input parameter $p\ge2$ (primality is not required). Two machines process the same word $x$, producing $a,b$ within time and space $W+1$. A converter maps $b$ to $d$ and a consumer maps the framed triple $(x,a,d)$ to $e$, each within time and space $(W+1)$ times one plus its respective input length. A single machine computes $e$ from $x$ within the Stage I bound at another fixed scale, independent of the input. This transfer isolates the copying, framing, and preservation of words between calls.
-- source:
--   S. Liu, B. Zhang and K. Ren, A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem, Zhejiang University preprint, 23 November 2026, Proposition 3.3 and its proof, Section 3.3.

import Definitions.Def_DetDLP_Machine

open DetDLP OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation

theorem DetDLP.m89_four_call_word_composition
    (A : PrimitiveMachine) (oa : Fin A.tapeCount) (B : PrimitiveMachine) (ob : Fin B.tapeCount)
    (D : PrimitiveMachine) (od : Fin D.tapeCount) (E : PrimitiveMachine) (oe : Fin E.tapeCount)
    (k : ℕ) : ∃ (M : PrimitiveMachine) (o : Fin M.tapeCount) (c : ℕ),
      ∀ (p : ℕ), 2 ≤ p → ∀ (x a b d e : List Bool),
        let W := mainSpaceBound k (bitLen p)
        let pack := Encoding.encodeList id [x,a,d]
        RunsWithin A oa x a (W+1) (W+1) → RunsWithin B ob x b (W+1) (W+1) →
        RunsWithin D od b d ((W+1)*(b.length+1)) ((W+1)*(b.length+1)) →
        RunsWithin E oe pack e ((W+1)*(pack.length+1)) ((W+1)*(pack.length+1)) →
        RunsWithin M o x e (mainSpaceBound c (bitLen p)) (mainSpaceBound c (bitLen p)) := by sorry
