-- Prove2me | Theorems.Thm_FOMCMonDep_theorem_4_2
-- name    : FOMCMonDep.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:26:08.133134+00:00
-- url     : https://prove2.me/theorems/37a7c9e9-2b28-4665-b1d3-57d8d8cc7dcb
-- title:
--   Theorem 4.2 — construction sequences of radius-$r$ depth-$q$ width $O(n^{\alpha\varepsilon})$ and length $O(n^{1+\alpha\varepsilon})$, computable in $\hat O(n^3)$
-- statement:
--   Let $\mathcal C$ be a monadically dependent graph class, $r,q\in\mathbb N$ and $\varepsilon>0$ a rational. There is a constant $\alpha\ge1$ depending only on $\mathcal C$ and $q$ such that every $n$-vertex graph $G\in\mathcal C$ has a construction sequence of radius-$r$ depth-$q$ width $O_{\mathcal C,r,q,\varepsilon}(n^{\alpha\varepsilon})$ and length $O_{\mathcal C,r,q,\varepsilon}(n^{1+\alpha\varepsilon})$. Moreover, an algorithm independent of $\mathcal C$ computes such a construction sequence from $r$, $q$, $\varepsilon$ and $G\in\mathcal C$ in time $\hat O_{\mathcal C,r,q,\varepsilon}(n^3)$.
--
--   That $\alpha$ does not depend on $\varepsilon$ makes the exponent $\alpha\varepsilon$ of the width as small as desired; this is the first half of the proof of Theorem 1.1.
--
--   **Formalization Note** $\alpha\ge1$ (a real number) is chosen after $\mathcal C$ and $q$ and before $r$ and $\varepsilon$; the constants of the width and length bounds after $\mathcal C,r,q,\varepsilon$; and the running time is, for every real $\varepsilon'>0$, at most $a'n^{3+\varepsilon'}+b'$ steps. The output carries the bounds of the existence clause.
--
--   Differences from the source:
--   - encoding: an algorithm (RAM model) → one program of the published TrulySubcubicAPSP word RAM with a word-size factor b, correct at every word size W ≥ b(⌊log₂(N+2)⌋+1), N the input length plus its largest absolute entry; reason: the paper's standard RAM with logarithmic word size; the exponents are RAM-specific
--   - encoding: a graph class (a set of finite graphs) → MonDepMW.GraphClass, the members on each vertex set Fin n; reason: every finite graph has a copy on some Fin n, and monadic dependence and all quantities are isomorphism invariant
--   - encoding: a construction sequence G1, …, Gλ of partial graphs → the list of its λ−1 steps on colors named by naturals, from G1 with color v = v; reason: Part III's own representation with named colors; any naming of the singleton parts is equivalent
--   - encoding: O_{C,r,q,ε}(n^{αε}), O_{C,r,q,ε}(n^{1+αε}), Ô_{C,r,q,ε}(n³) → a·n^{αε} + b, a·n^{1+αε} + b, and ∀ ε′ > 0, ⌊a′·n^{3+ε′} + b′⌋ steps; reason: the asymptotic convention of §3, p.11
--   - reading: computes such a construction sequence → the output satisfies the existence clause with the same constants; reason: the natural (stronger) reading of 'such'
--   - encoding: r, q, a rational ε and G as input; a construction sequence as output → graphInput G, r, q, num ε, den ε; the output cells begin with seqCode of the sequence (its number of steps, then one code [0|1|2, P, Q] per step); reason: fixed input/output layout of the mission; the paper fixes none
-- source:
--   Dreier, Mählmann, Toruńczyk, First-Order Model Checking on Monadically Dependent Graph Classes, STOC 2027 submission (held manuscript, sha256 98040ab52fa9eeb6577af7e100d83ff2a156142fed0a0178723cec8569510454), Theorem 4.2, p.13 (PDF 15)

import Mathlib
import Definitions.Def_TrulySubcubicAPSP_WordRAM
import Definitions.Def_MonDepMW_RunsWithin
import Definitions.Def_MonDepMW_MonadicallyDependent
import Definitions.Def_FOMCMonDep_DecidesWithin
import Definitions.Def_FOMCMonDep_ConstructionSeq

set_option autoImplicit false

open TrulySubcubicAPSP

namespace FOMCMonDep

/-- **Theorem 4.2.** Dreier, Mählmann, Toruńczyk, *First-Order Model Checking on Monadically Dependent Graph Classes*, STOC 2027 submission (held manuscript, sha256 98040ab5…), §4, p.13 (PDF 15); proof p.16 (PDF 18): "Let 𝒞 be a monadically
dependent graph class, r, q ∈ N, and let ε > 0 be a rational. There is a constant α ⩾ 1 depending only on 𝒞 and q such
that every n-vertex graph G ∈ 𝒞 has a construction sequence of radius-r depth-q width O_{𝒞,r,q,ε}(n^{αε}) and length
O_{𝒞,r,q,ε}(n^{1+αε}). Moreover, there is an algorithm (independent of 𝒞) which, given r, q ∈ N, a rational ε > 0,
and an n-vertex graph G ∈ 𝒞, computes such a construction sequence in time Ô_{𝒞,r,q,ε}(n³)."

**Formalization Note.** Constant order: the program `P` (with word-size factor `bw`) first; then `𝒞` and `q`; then
`α ⩾ 1` (real), before `r` and `ε` (p.13: "It is important that α does not depend on ε"); then `a, b` after
`𝒞, r, q, ε`; the time constants `a′, b′` after `𝒞, r, q, ε` and `ε′` (`Ô`: for every `ε′ > 0`,
`a′ · n^{3+ε′} + b′` steps). Input: `graphInput G`, `r`, `q`, then `ε` as numerator and denominator; output: the
code of the sequence, accepted. "Such a construction sequence" carries the same bounds as the existence clause. -/
theorem theorem_4_2 :
    ∃ (P : List Instr) (bw : ℕ), ∀ 𝒞 : MonDepMW.GraphClass, MonDepMW.MonadicallyDependent 𝒞 →
      ∀ q : ℕ, ∃ α : ℝ, 1 ≤ α ∧ ∀ r : ℕ, ∀ ε : ℚ, 0 < ε → ∃ a b : ℕ,
        (∀ (n : ℕ) (G : SimpleGraph (Fin n)), G ∈ 𝒞 n →
          ∃ seq : List Step, IsConstructionSeq G seq ∧
            (depthWidth (n := n) seq r q : ℝ) ≤ (a : ℝ) * (n : ℝ) ^ (α * ε) + b ∧
            (seqLength seq : ℝ) ≤ (a : ℝ) * (n : ℝ) ^ (1 + α * ε) + b) ∧
        ∀ ε' : ℝ, 0 < ε' → ∃ a' b' : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G ∈ 𝒞 n →
          ∀ W : ℕ, WordSizeOK bw (MonDepMW.graphInput G ++ (r : ℤ) :: (q : ℤ) :: ratCode ε) W →
            MonDepMW.RunsWithin P W ⌊(a' : ℝ) * (n : ℝ) ^ (3 + ε') + b'⌋₊
              (MonDepMW.graphInput G ++ (r : ℤ) :: (q : ℤ) :: ratCode ε) fun out =>
                ∃ seq : List Step, Emits out (seqCode seq) ∧ IsConstructionSeq G seq ∧
                  (depthWidth (n := n) seq r q : ℝ) ≤ (a : ℝ) * (n : ℝ) ^ (α * ε) + b ∧
                  (seqLength seq : ℝ) ≤ (a : ℝ) * (n : ℝ) ^ (1 + α * ε) + b := by sorry

end FOMCMonDep
