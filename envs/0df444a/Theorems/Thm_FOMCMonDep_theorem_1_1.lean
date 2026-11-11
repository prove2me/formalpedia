-- Prove2me | Theorems.Thm_FOMCMonDep_theorem_1_1
-- name    : FOMCMonDep.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:23:35.679986+00:00
-- url     : https://prove2.me/theorems/4f1af198-b826-41d7-8e5d-c271e3a36f7d
-- title:
--   Theorem 1.1 — first-order model checking in time $O_{\mathcal C,\varphi,\varepsilon}(n^{3+\varepsilon})$ on every monadically dependent class, by one uniform algorithm
-- statement:
--   There is an algorithm which solves the model checking problem for first-order logic on graphs, that is, decides for a given finite graph $G$ and a given first-order sentence $\varphi$ whether $G\models\varphi$, with the following guarantee: for every monadically dependent graph class $\mathcal C$ and every real $\varepsilon>0$, the algorithm runs in time
--   $$O_{\mathcal C,\varphi,\varepsilon}\bigl(n^{3+\varepsilon}\bigr)$$
--   on $n$-vertex graphs $G\in\mathcal C$.
--
--   The algorithm is uniform: it takes both $G$ and $\varphi$ as input and does not depend on $\mathcal C$, which only appears in the running-time guarantee; the constants hidden in the $O$ need not be computable. With the hardness result of Dreier, Mählmann and Toruńczyk (2024), this confirms the Model Checking Conjecture: a hereditary graph class admits fixed-parameter tractable first-order model checking if and only if it is monadically dependent (assuming $\mathrm{FPT}\ne\mathrm{AW}[\star]$).
--
--   **Formalization Note** The algorithm is one word-RAM program with a word-size factor, both fixed before $\mathcal C$, $\varphi$ and $\varepsilon$. Clause (i): on every finite graph and every sentence the program halts with the correct verdict. Clause (ii): for every monadically dependent class, every sentence and every real $\varepsilon>0$ there are $a,c$ such that the program halts with the correct verdict within $\lfloor a n^{3+\varepsilon}+c\rfloor$ steps on every $n$-vertex member. The input is the adjacency matrix of $G$ followed by the prefix code of $\varphi$; $n$ is the number of vertices.
--
--   Differences from the source:
--   - encoding: an algorithm (RAM model) → one program of the published TrulySubcubicAPSP word RAM with a word-size factor b, correct at every word size W ≥ b(⌊log₂(N+2)⌋+1), N the input length plus its largest absolute entry; reason: the paper's standard RAM with logarithmic word size; the exponents are RAM-specific
--   - encoding: a graph class (a set of finite graphs) → MonDepMW.GraphClass, the members on each vertex set Fin n; reason: every finite graph has a copy on some Fin n, and monadic dependence and all quantities are isomorphism invariant
--   - encoding: G and φ as input → graphInput G (n, then the n² adjacency bits) followed by encSentence φ (an injective prefix code); reason: the paper fixes no input format
--   - encoding: O_{C,φ,ε}(n^{3+ε}) → ⌊a·n^{3+ε} + c⌋ steps with a, c ∈ ℕ chosen after C, φ, ε; reason: the asymptotic convention of §3, p.11
-- source:
--   Dreier, Mählmann, Toruńczyk, First-Order Model Checking on Monadically Dependent Graph Classes, STOC 2027 submission (held manuscript, sha256 98040ab52fa9eeb6577af7e100d83ff2a156142fed0a0178723cec8569510454), Theorem 1.1, p.2 (PDF 4)

import Mathlib
import Definitions.Def_TrulySubcubicAPSP_WordRAM
import Definitions.Def_MonDepMW_RunsWithin
import Definitions.Def_MonDepMW_MonadicallyDependent
import Definitions.Def_FOMCMonDep_encSentence
import Definitions.Def_FOMCMonDep_DecidesWithin

set_option autoImplicit false

open TrulySubcubicAPSP FirstOrder FirstOrder.Language

namespace FOMCMonDep

/-- **Theorem 1.1.** Dreier, Mählmann, Toruńczyk, *First-Order Model Checking on Monadically Dependent Graph Classes*, STOC 2027 submission (held manuscript, sha256 98040ab5…), §1.1, p.2 (PDF 4); restated and proved pp.13–14 (PDF 15–16): "There
is an algorithm which solves the model checking problem for first-order logic on graphs – does a given graph G satisfy
a given first-order sentence φ? – with the following guarantee. For every monadically dependent graph class 𝒞 and real
ε > 0, the algorithm runs in time O_{𝒞,φ,ε}(n^{3+ε}) for n-vertex graphs G ∈ 𝒞." Footnote 1, p.1 (PDF 3): "the
function f need not be computable, but there is a single algorithm which solves the problem, independent of the
parameter (φ in the case of model checking)"; p.2: "our algorithm is uniform: it takes both G and φ as input, and does
not depend on the graph class 𝒞, which only appears in the running-time guarantee."

**Formalization Note.** The algorithm is one program `P` of the published `TrulySubcubicAPSP` word RAM, with a
word-size factor `b`, both chosen before `𝒞`, `φ` and `ε`; it must be correct at every word size above
`b · (⌊log₂(N + 2)⌋ + 1)`, `N` the input size (`WordSizeOK`). Input: `graphInput G` (`n`, then the `n²` adjacency
bits) followed by the prefix code `encSentence φ`. Clause (i): on every finite graph and every sentence, `P` halts
with the correct verdict ("solves the model checking problem"). Clause (ii): for every monadically dependent class
`𝒞` (the published `MonDepMW.GraphClass`, members on each `Fin n`), every `φ` and every real `ε > 0`, there are
`a, c` (depending on `𝒞, φ, ε`; not necessarily computable) such that `P` halts with the correct verdict within
`⌊a · n^{3+ε} + c⌋` steps on every `n`-vertex `G ∈ 𝒞`. `n` is the vertex count, not the input length. -/
theorem theorem_1_1 :
    ∃ (P : List Instr) (b : ℕ),
      (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (φ : Language.graph.Sentence) (W : ℕ),
        WordSizeOK b (MonDepMW.graphInput G ++ encSentence φ) W →
          ∃ t : ℕ, DecidesWithin P W t (MonDepMW.graphInput G ++ encSentence φ)
            (@Sentence.Realize Language.graph (Fin n) G.structure φ)) ∧
      (∀ 𝒞 : MonDepMW.GraphClass, MonDepMW.MonadicallyDependent 𝒞 →
        ∀ (φ : Language.graph.Sentence) (ε : ℝ), 0 < ε → ∃ a c : ℕ,
          ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G ∈ 𝒞 n →
            ∀ W : ℕ, WordSizeOK b (MonDepMW.graphInput G ++ encSentence φ) W →
              DecidesWithin P W ⌊(a : ℝ) * (n : ℝ) ^ (3 + ε) + c⌋₊ (MonDepMW.graphInput G ++ encSentence φ)
                (@Sentence.Realize Language.graph (Fin n) G.structure φ)) := by sorry

end FOMCMonDep
