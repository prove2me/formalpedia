-- Prove2me | Theorems.Thm_FOMCMonDep_Supplement_theorem_4_8
-- name    : FOMCMonDep.Supplement.theorem_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:18:41.501235+00:00
-- url     : https://prove2.me/theorems/78f87dc8-5442-4686-a282-c5fd8568b95f
-- title:
--   Theorem 4.8 — in nowhere dense classes, radius-$r$ definable construction sequences with one predicate, $O(n^{\varepsilon})$ parameters and rank $0$, computable in time $O(n^{1+\varepsilon})$
-- statement:
--   Let $\mathcal C$ be a nowhere dense graph class, $r\in\mathbb N$ and $\varepsilon>0$ a real number. There are $a,b\in\mathbb N$, depending only on $\mathcal C$, $r$ and $\varepsilon$, such that:
--
--   1. every $n$-vertex graph $G\in\mathcal C$ has a construction sequence $G_1,\dots,G_\lambda$ that is radius-$r$ definable with one unary predicate, at most $\lfloor a\,n^{\varepsilon}+b\rfloor$ parameters and quantifier rank $0$, and whose length satisfies
--   $$
--   \lambda\le a\,n^{1+\varepsilon}+b;
--   $$
--   2. there is a word-RAM program which, given an $n$-vertex graph $G\in\mathcal C$ by adjacency lists, outputs such a sequence (with the same $a,b$) within $a'\,n^{1+\varepsilon}+b'$ steps, where $a',b'$ also depend only on $\mathcal C$, $r$ and $\varepsilon$.
--
--   Together with Parts I and III of the paper, this gives an alternative proof that first-order model checking is fixed-parameter tractable on nowhere dense classes (Grohe, Kreutzer and Siebertz).
--
--   **Formalization Note** The program, its word-size factor and the time constants are chosen after $\mathcal C,r,\varepsilon$, because the theorem claims no uniformity. The program must be correct at every word size above a logarithmic threshold and for every valid ordering of the adjacency lists. Its output cells begin with the code of the sequence. Quantifier rank $0$ means quantifier-free.
--
--   Differences from the source:
--   - encoding: an algorithm (RAM model) → a program of the published TrulySubcubicAPSP word RAM with a word-size factor bw, correct at every word size W ≥ bw(⌊log₂(N+2)⌋+1), N the input length plus its largest absolute entry; reason: the paper's standard RAM with logarithmic word size, as in the base mission
--   - encoding: a graph class (a set of finite graphs) → MonDepMW.GraphClass, the members on each vertex set Fin n; reason: every finite graph has a copy on some Fin n; nowhere density and all quantities are isomorphism invariant
--   - encoding: nowhere dense (cited from [NO11; GKS17], not defined in the paper) → for every r there is t with no ≤2r-subdivision of K_t as a subgraph of a member; reason: the standard definition; all its variants define the same classes
--   - encoding: O_{C,r,ε}(n^ε) parameters, length O_{C,r,ε}(n^{1+ε}), time O_{C,r,ε}(n^{1+ε}) → ⌊a·n^ε + b⌋ parameters, length ≤ a·n^{1+ε} + b, ⌊a′·n^{1+ε} + b′⌋ steps, with a, b, a′, b′ ∈ ℕ chosen after C, r, ε; reason: the asymptotic convention of §3, p.10
--   - reading: such a sequence can be computed; quantifier rank 0 → the output satisfies the existence clause with the same a, b; quantifier rank at most 0 (quantifier-free); reason: the natural reading of 'such'; rank is read as 'at most' throughout the mission
--   - encoding: G as input, a construction sequence as output → the published FourColorLinear.encodeAdj adj (n, then degree and neighbours of each vertex), cast to ℤ, for every adj with FourColorLinear.AdjacencyLists G adj (any order); the output cells begin with seqCode of the sequence; reason: App. C, p.63 computes on adjacency lists; the paper fixes no layout
-- source:
--   Dreier, Mählmann, Toruńczyk, First-Order Model Checking on Monadically Dependent Graph Classes, STOC 2027 submission (held manuscript, sha256 98040ab52fa9eeb6577af7e100d83ff2a156142fed0a0178723cec8569510454), Theorem 4.8, p.15 (PDF 17); restated p.62 (PDF 64), proof sketch p.63 (PDF 65)

import Mathlib
import Definitions.Def_TrulySubcubicAPSP_WordRAM
import Definitions.Def_MonDepMW_RunsWithin
import Definitions.Def_MonDepMW_MonadicallyDependent
import Definitions.Def_FOMCMonDep_DecidesWithin
import Definitions.Def_FOMCMonDep_RadiusDefinable
import Definitions.Def_FOMCMonDep_Supplement_NowhereDense
import Definitions.Def_FourColorLinear_encodeAdj

set_option autoImplicit false

open TrulySubcubicAPSP

namespace FOMCMonDep.Supplement

/-- **Theorem 4.8.** Dreier, Mählmann, Toruńczyk, *First-Order Model Checking on Monadically Dependent Graph Classes*,
STOC 2027 submission (held manuscript, sha256 98040ab5…), §4.1.2, p.15 (PDF 17); restated p.62 (PDF 64), proof
sketch p.63 (PDF 65):
"Let 𝒞 be a nowhere dense graph class, r ∈ N, and ε > 0. Every n-vertex graph G ∈ 𝒞 has a radius-r definable
construction sequence with one unary predicate, O_{𝒞,r,ε}(n^ε) parameters, quantifier rank 0, and length
O_{𝒞,r,ε}(n^{1+ε}). Such a sequence can be computed in time O_{𝒞,r,ε}(n^{1+ε})."

**Formalization Note.** Constant order, as printed (no uniformity is claimed): `𝒞`, `r` (`r = 0` allowed) and a real
`ε > 0` first; then `a, b ∈ ℕ` for the parameter and length bounds (`O_k(f)` is `a · f + b`, §3, p.10); then the
program `P` of the published word RAM, its word-size factor `bw` and the time constants `a′, b′`. The program reads
`G` as adjacency lists in any valid order (App. C, p.63: an `O(n^{1+ε})` bound is impossible on an `n × n`
adjacency matrix): the published `FourColorLinear.AdjacencyLists` / `encodeAdj` (`n`, then for each vertex its
degree and its neighbours), with the words cast to `ℤ` for the RAM; is correct at every word size `W` above the threshold `WordSizeOK bw`, accepts within
`⌊a′ · n^{1+ε} + b′⌋₊` steps (`n` the vertex count) and outputs the code of a sequence carrying all the bounds of the
existence clause with the same `a, b` ("Such a sequence"). "Quantifier rank 0" is quantifier rank at most `0`, i.e.
quantifier-free; parameters are counted with `⌊a · n^ε + b⌋₊`. -/
theorem theorem_4_8 :
    ∀ 𝒞 : MonDepMW.GraphClass, NowhereDense 𝒞 → ∀ r : ℕ, ∀ ε : ℝ, 0 < ε → ∃ a b : ℕ,
      (∀ (n : ℕ) (G : SimpleGraph (Fin n)), G ∈ 𝒞 n →
        ∃ seq : List Step, IsConstructionSeq G seq ∧
          RadiusDefinable G seq r 1 ⌊(a : ℝ) * (n : ℝ) ^ ε + b⌋₊ 0 ∧
          (seqLength seq : ℝ) ≤ (a : ℝ) * (n : ℝ) ^ (1 + ε) + b) ∧
      ∃ (P : List Instr) (bw a' b' : ℕ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G ∈ 𝒞 n →
        ∀ adj : Fin n → List (Fin n), FourColorLinear.AdjacencyLists G adj →
          ∀ W : ℕ, WordSizeOK bw ((FourColorLinear.encodeAdj adj).map fun x : ℕ => (x : ℤ)) W →
            MonDepMW.RunsWithin P W ⌊(a' : ℝ) * (n : ℝ) ^ (1 + ε) + b'⌋₊
              ((FourColorLinear.encodeAdj adj).map fun x : ℕ => (x : ℤ)) fun out =>
              ∃ seq : List Step, Emits out (seqCode seq) ∧ IsConstructionSeq G seq ∧
                RadiusDefinable G seq r 1 ⌊(a : ℝ) * (n : ℝ) ^ ε + b⌋₊ 0 ∧
                (seqLength seq : ℝ) ≤ (a : ℝ) * (n : ℝ) ^ (1 + ε) + b := by sorry

end FOMCMonDep.Supplement
