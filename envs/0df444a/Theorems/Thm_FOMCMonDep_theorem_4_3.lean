-- Prove2me | Theorems.Thm_FOMCMonDep_theorem_4_3
-- name    : FOMCMonDep.theorem_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:26:36.142746+00:00
-- url     : https://prove2.me/theorems/2b391f07-cd91-4d1e-b5d8-cabcc7d1a1b7
-- title:
--   Theorem 4.3 — model checking along a construction sequence in time $\lambda\cdot n^2\cdot\mathrm{poly}_\varphi(K)$
-- statement:
--   There is an algorithm which, given a sentence $\varphi$ and an $n$-vertex graph $G$ together with a construction sequence of $G$ of length $\lambda$, determines whether $G\models\varphi$ in time
--   $$\lambda\cdot n^2\cdot\mathrm{poly}_\varphi(K),$$
--   where $K$ is the radius-$r$ depth-$d$ width of the construction sequence for numbers $r$ and $d$ computable from $\varphi$; one can take $r=\rho^+(1,q)=9^{(1+q)(q+1)}$ and $d=r+1+q$, where $q$ is the quantifier rank of $\varphi$.
--
--   This is the second half of the proof of Theorem 1.1, the dynamic programming with type trees of Part III.
--
--   **Formalization Note** One program for all sentences. Input: the adjacency matrix of $G$, the code of $\varphi$ and the code of the construction sequence. The time is $a\lambda n^2(K+2)^e+c$ with $a,c,e$ depending on $\varphi$.
--
--   Differences from the source:
--   - encoding: an algorithm (RAM model) → one program of the published TrulySubcubicAPSP word RAM with a word-size factor b, correct at every word size W ≥ b(⌊log₂(N+2)⌋+1), N the input length plus its largest absolute entry; reason: the paper's standard RAM with logarithmic word size; the exponents are RAM-specific
--   - encoding: a construction sequence G1, …, Gλ of partial graphs → the list of its λ−1 steps on colors named by naturals, from G1 with color v = v; reason: Part III's own representation with named colors; any naming of the singleton parts is equivalent
--   - generalization: for some r and q (p.38: d) computable from φ → r = ρ⁺(1, qrank φ) and d = r + 1 + qrank φ, explicitly; reason: these are the values of the proof (p.51); explicit computable functions of φ specialize to the existential claim
--   - reading: time λ · n² · poly_φ(K) → a·λ·n²·(K + 2)^e + c steps with a, c, e after φ; reason: poly is (x + 2)^{O(1)} (§3); the additive c covers n = 0, where the proof evaluates φ directly (p.51)
--   - encoding: φ, G and its construction sequence as input → graphInput G, then encSentence φ (an injective prefix code), then seqCode of the sequence; reason: fixed input layout of the mission; the paper fixes none
-- source:
--   Dreier, Mählmann, Toruńczyk, First-Order Model Checking on Monadically Dependent Graph Classes, STOC 2027 submission (held manuscript, sha256 98040ab52fa9eeb6577af7e100d83ff2a156142fed0a0178723cec8569510454), Theorem 4.3, p.13 (PDF 15)

import Mathlib
import Definitions.Def_TrulySubcubicAPSP_WordRAM
import Definitions.Def_MonDepMW_RunsWithin
import Definitions.Def_FOMCMonDep_qrank
import Definitions.Def_FOMCMonDep_encSentence
import Definitions.Def_FOMCMonDep_DecidesWithin
import Definitions.Def_FOMCMonDep_ConstructionSeq
import Definitions.Def_FOMCMonDep_treeCode

set_option autoImplicit false

open TrulySubcubicAPSP FirstOrder FirstOrder.Language

namespace FOMCMonDep

/-- **Theorem 4.3.** Dreier, Mählmann, Toruńczyk, *First-Order Model Checking on Monadically Dependent Graph Classes*, STOC 2027 submission (held manuscript, sha256 98040ab5…), §4, p.13 (PDF 15); restated Part III, p.38 (PDF 40), proof
pp.50–51 (PDF 52–53): "There is an algorithm which, given a sentence φ and an n-vertex graph G together with its
construction sequence of length λ, determines whether G |= φ in time λ · n² · poly_φ(K), where K is the radius-r
depth-q width of the construction sequence, for some r and q which are computable from φ." (p.38: "radius-r depth-d
width […] for some r and d".)

**Formalization Note.** One program `P` (with word-size factor `bw`) for all sentences. `r` and `d` are given
explicitly, as in the proof (p.51: "let r, d be as in Lemma 13.1 for k = 1 and this q"): `r = ρ⁺(1, q)` and
`d = r + 1 + q` with `q` the quantifier rank of `φ`; explicit functions of `φ` are computable. Input:
`graphInput G`, the code of `φ`, then the code of the construction sequence; the verdict is `G ⊨ φ` (Mathlib
semantics of `Language.graph` sentences on `G.structure`). The time is `a · λ · n² · (K + 2)^e + c` with `a, c, e`
after `φ`: `poly_φ(K)` is `(K + 2)^e`, `a` is absorbed by it, and `c` covers `n = 0` (p.51: "If n ⩽ 1, evaluate φ
directly"). -/
theorem theorem_4_3 :
    ∃ (P : List Instr) (bw : ℕ), ∀ φ : Language.graph.Sentence, ∃ a c e : ℕ,
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (seq : List Step), IsConstructionSeq G seq →
        ∀ W : ℕ, WordSizeOK bw (MonDepMW.graphInput G ++ encSentence φ ++ seqCode seq) W →
          DecidesWithin P W
            (a * seqLength seq * n ^ 2 *
                (depthWidth (n := n) seq (rhoPlus 1 (qrank φ)) (rhoPlus 1 (qrank φ) + 1 + qrank φ) + 2) ^ e + c)
            (MonDepMW.graphInput G ++ encSentence φ ++ seqCode seq)
            (@Sentence.Realize Language.graph (Fin n) G.structure φ) := by sorry

end FOMCMonDep
