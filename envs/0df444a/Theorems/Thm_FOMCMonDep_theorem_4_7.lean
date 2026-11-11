-- Prove2me | Theorems.Thm_FOMCMonDep_theorem_4_7
-- name    : FOMCMonDep.theorem_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:28:53.998194+00:00
-- url     : https://prove2.me/theorems/01a51cf5-63ff-4b0f-b2ad-b433e33a3f82
-- title:
--   Theorem 4.7 — radius-$r$ definable construction sequences with $O(r/\varepsilon)$ predicates, $O(n^{\delta\varepsilon})$ parameters and rank $7$, computable in $\hat O(n^3)$
-- statement:
--   Let $r\ge1$ be an integer, $\varepsilon>0$ a rational and $\mathcal C$ a monadically dependent graph class. There is a constant $\delta\ge1$ depending only on $\mathcal C$ such that every $n$-vertex graph $G\in\mathcal C$ has a construction sequence which is radius-$r$ definable with $O(r/\varepsilon)$ unary predicates, $O_{\mathcal C,r,\varepsilon}(n^{\delta\varepsilon})$ parameters and quantifier rank $7$, and has length $O_{\mathcal C,r,\varepsilon}(n^{1+\delta\varepsilon})$. Moreover, an algorithm independent of $\mathcal C$ computes such a sequence from $r$, $\varepsilon$ and $G$ in time $\hat O_{\mathcal C,r,\varepsilon}(n^3)$ whenever $G\in\mathcal C$.
--
--   This is the key result of Part II, used in the proof of Theorem 4.2.
--
--   **Formalization Note** The constants of $O(r/\varepsilon)$ are absolute; $\delta\ge1$ (a real number) is chosen after $\mathcal C$ and before $r,\varepsilon$; the constants of the parameter and length bounds after $\mathcal C,r,\varepsilon$; and $\hat O_{\mathcal C,r,\varepsilon}(n^3)$ means: for every real $\varepsilon'>0$, at most $a'n^{3+\varepsilon'}+b'$ steps. The output carries the bounds of the existence clause.
--
--   Differences from the source:
--   - encoding: an algorithm (RAM model) → one program of the published TrulySubcubicAPSP word RAM with a word-size factor b, correct at every word size W ≥ b(⌊log₂(N+2)⌋+1), N the input length plus its largest absolute entry; reason: the paper's standard RAM with logarithmic word size; the exponents are RAM-specific
--   - encoding: a graph class (a set of finite graphs) → MonDepMW.GraphClass, the members on each vertex set Fin n; reason: every finite graph has a copy on some Fin n, and monadic dependence and all quantities are isomorphism invariant
--   - encoding: a construction sequence G1, …, Gλ of partial graphs → the list of its λ−1 steps on colors named by naturals, from G1 with color v = v; reason: Part III's own representation with named colors; any naming of the singleton parts is equivalent
--   - encoding: O(r/ε), O_{C,r,ε}(n^{δε}), O_{C,r,ε}(n^{1+δε}), Ô_{C,r,ε}(n³) → ⌊a0·r/ε + b0⌋ predicates, ⌊a·n^{δε} + b⌋ parameters, length ≤ a·n^{1+δε} + b, and ∀ ε′ > 0, ⌊a′·n^{3+ε′} + b′⌋ steps; reason: the asymptotic convention of §3, p.11
--   - reading: computes such a sequence; quantifier rank 7 → the output satisfies the existence clause with the same constants; quantifier rank at most 7; reason: the natural (stronger) reading of 'such'; a formula of smaller rank pads to rank 7
--   - encoding: r, a rational ε and G as input; a construction sequence as output → graphInput G, r, num ε, den ε; the output cells begin with seqCode of the sequence; reason: fixed input/output layout of the mission; the paper fixes none
-- source:
--   Dreier, Mählmann, Toruńczyk, First-Order Model Checking on Monadically Dependent Graph Classes, STOC 2027 submission (held manuscript, sha256 98040ab52fa9eeb6577af7e100d83ff2a156142fed0a0178723cec8569510454), Theorem 4.7, p.14 (PDF 16)

import Mathlib
import Definitions.Def_TrulySubcubicAPSP_WordRAM
import Definitions.Def_MonDepMW_RunsWithin
import Definitions.Def_MonDepMW_MonadicallyDependent
import Definitions.Def_FOMCMonDep_DecidesWithin
import Definitions.Def_FOMCMonDep_RadiusDefinable

set_option autoImplicit false

open TrulySubcubicAPSP

namespace FOMCMonDep

/-- **Theorem 4.7.** Dreier, Mählmann, Toruńczyk, *First-Order Model Checking on Monadically Dependent Graph Classes*, STOC 2027 submission (held manuscript, sha256 98040ab5…), §4.1.2, p.14 (PDF 16); restated p.28 (PDF 30), proof p.29 (PDF 31):
"Let r ⩾ 1 be an integer, ε > 0 be a rational, and 𝒞 be a monadically dependent graph class. There is a constant δ ⩾ 1
depending only on 𝒞 such that every n-vertex graph G ∈ 𝒞 has a construction sequence of G which is radius-r definable
with O(r/ε) unary predicates, O_{𝒞,r,ε}(n^{δε}) parameters, and quantifier rank 7, and has length O_{𝒞,r,ε}(n^{1+δε}).
Moreover, there is an algorithm (independent of 𝒞) which, given r, ε, and G, computes such a sequence, and runs in time
Ô_{𝒞,r,ε}(n³) whenever G ∈ 𝒞."

**Formalization Note.** Constant order: the absolute constants `a₀, b₀` of `O(r/ε)` and the program `P` (with its
word-size factor `bw`) first; then `𝒞`; then `δ ⩾ 1` (real), before `r` and `ε`; then `a, b` after `𝒞, r, ε`
for the parameters and the length; the time constants `a′, b′` after `𝒞, r, ε` and `ε′` (`Ô`: for every
`ε′ > 0`, `a′ · n^{3+ε′} + b′` steps). Predicates and parameters are counted with `⌊·⌋₊` of the bounds (definable
with fewer is definable with more). Input: `graphInput G`, `r`, then `ε` as numerator and denominator; output: the
code of the sequence, accepted. "Such a sequence" carries the same bounds as the existence clause. -/
theorem theorem_4_7 :
    ∃ a₀ b₀ : ℕ, ∃ (P : List Instr) (bw : ℕ), ∀ 𝒞 : MonDepMW.GraphClass, MonDepMW.MonadicallyDependent 𝒞 →
      ∃ δ : ℝ, 1 ≤ δ ∧ ∀ r : ℕ, 1 ≤ r → ∀ ε : ℚ, 0 < ε → ∃ a b : ℕ,
        (∀ (n : ℕ) (G : SimpleGraph (Fin n)), G ∈ 𝒞 n →
          ∃ seq : List Step, IsConstructionSeq G seq ∧
            RadiusDefinable G seq r ⌊(a₀ : ℝ) * r / (ε : ℝ) + b₀⌋₊ ⌊(a : ℝ) * (n : ℝ) ^ (δ * ε) + b⌋₊ 7 ∧
            (seqLength seq : ℝ) ≤ (a : ℝ) * (n : ℝ) ^ (1 + δ * ε) + b) ∧
        ∀ ε' : ℝ, 0 < ε' → ∃ a' b' : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G ∈ 𝒞 n →
          ∀ W : ℕ, WordSizeOK bw (MonDepMW.graphInput G ++ (r : ℤ) :: ratCode ε) W →
            MonDepMW.RunsWithin P W ⌊(a' : ℝ) * (n : ℝ) ^ (3 + ε') + b'⌋₊
              (MonDepMW.graphInput G ++ (r : ℤ) :: ratCode ε) fun out =>
                ∃ seq : List Step, Emits out (seqCode seq) ∧ IsConstructionSeq G seq ∧
                  RadiusDefinable G seq r ⌊(a₀ : ℝ) * r / (ε : ℝ) + b₀⌋₊ ⌊(a : ℝ) * (n : ℝ) ^ (δ * ε) + b⌋₊ 7 ∧
                  (seqLength seq : ℝ) ≤ (a : ℝ) * (n : ℝ) ^ (1 + δ * ε) + b := by sorry

end FOMCMonDep
