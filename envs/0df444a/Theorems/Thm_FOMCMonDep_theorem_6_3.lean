-- Prove2me | Theorems.Thm_FOMCMonDep_theorem_6_3
-- name    : FOMCMonDep.theorem_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:24:54.578204+00:00
-- url     : https://prove2.me/theorems/949fa5b1-e982-4bce-8641-38416748d609
-- title:
--   Theorem 6.3 ([Dre+26, Theorem 4.4]) — chains of length $O(r/\varepsilon)$ and radius-$r$ width $O_{\mathcal C,r,\varepsilon}(n^\varepsilon)$ in time $\hat O_{\mathcal C,r}(n^3)$
-- statement:
--   There is an algorithm which, given an $n$-vertex graph $G$, a radius $r\in\mathbb N$ and a rational $\varepsilon>0$, computes a chain of $G$ of length $O(r/\varepsilon)$ and radius-$r$ width $O_{\mathcal C,r,\varepsilon}(n^\varepsilon)$, and runs in time $\hat O_{\mathcal C,r}(n^3)$, where $\mathcal C$ is any monadically dependent graph class containing $G$.
--
--   This is the main result of the companion paper (Dreier, Mählmann, Pilipczuk, Toruńczyk, arXiv:2611.06804, Theorem 4.4), used here as the source of the decompositions.
--
--   **Formalization Note** One program for all classes, radii and $\varepsilon$; its input is the adjacency matrix of $G$, then $r$, then the numerator and denominator of $\varepsilon$, and its output is the code of the chain. The length bound $a_0 r/\varepsilon+b_0$ has absolute constants. The running time $\hat O_{\mathcal C,r}(n^3)$ means: for every real $\varepsilon'>0$, at most $a'n^{3+\varepsilon'}+b'$ steps with $a',b'$ depending on $\mathcal C,r,\varepsilon'$ but not on $\varepsilon$, as printed. The width constants depend on $\mathcal C,r,\varepsilon$.
--
--   Differences from the source:
--   - encoding: an algorithm (RAM model) → one program of the published TrulySubcubicAPSP word RAM with a word-size factor b, correct at every word size W ≥ b(⌊log₂(N+2)⌋+1), N the input length plus its largest absolute entry; reason: the paper's standard RAM with logarithmic word size; the exponents are RAM-specific
--   - encoding: a graph class (a set of finite graphs) → MonDepMW.GraphClass, the members on each vertex set Fin n; reason: every finite graph has a copy on some Fin n, and monadic dependence and all quantities are isomorphism invariant
--   - encoding: G, r and a rational ε as input; a chain as output → graphInput G, r, num ε, den ε; the output cells begin with chainCode of a chain; reason: fixed input/output layout of the mission
--   - encoding: O(r/ε), O_{C,r,ε}(n^ε), Ô_{C,r}(n³) → a0·r/ε + b0 (absolute); a·n^ε + b (after C, r, ε); ∀ ε′ > 0, ⌊a′·n^{3+ε′} + b′⌋ (after C, r, ε′, before ε); reason: the asymptotic convention of §3, p.11; the width constants are also after ε′, which changes nothing since the output does not depend on ε′
-- source:
--   Dreier, Mählmann, Toruńczyk, First-Order Model Checking on Monadically Dependent Graph Classes, STOC 2027 submission (held manuscript, sha256 98040ab52fa9eeb6577af7e100d83ff2a156142fed0a0178723cec8569510454), Theorem 6.3, p.28 (PDF 30)

import Mathlib
import Definitions.Def_TrulySubcubicAPSP_WordRAM
import Definitions.Def_MonDepMW_RunsWithin
import Definitions.Def_MonDepMW_MonadicallyDependent
import Definitions.Def_FOMCMonDep_DecidesWithin
import Definitions.Def_FOMCMonDep_Chain

set_option autoImplicit false

open TrulySubcubicAPSP

namespace FOMCMonDep

/-- **Theorem 6.3 ([Dre+26, Theorem 4.4]).** Dreier, Mählmann, Toruńczyk, *First-Order Model Checking on Monadically Dependent Graph Classes*, STOC 2027 submission (held manuscript, sha256 98040ab5…), §6, p.28 (PDF 30): "There is an algorithm
which, given an n-vertex graph G, radius r ∈ N, and rational ε > 0, computes a chain of G of length O(r/ε) and radius-r
width O_{𝒞,r,ε}(n^ε), and runs in time Ô_{𝒞,r}(n³), where 𝒞 is any monadically dependent graph class containing G."

**Formalization Note.** One program `P` (with its word-size factor `bw`) for all classes, radii and `ε`, on the
published `TrulySubcubicAPSP` word RAM. Input: `graphInput G` (`n`, then the adjacency matrix), `r`, and `ε` as
numerator and denominator; it must work at every word size above `WordSizeOK`. Output: the code of a chain (`ℓ`, then
`ℓ` blocks of `n` bits), accepted. `O(r/ε)` has absolute constants `a₀, b₀`. `Ô_{𝒞,r}(n³)` is: for every real
`ε′ > 0`, at most `a′ · n^{3+ε′} + b′` steps, with `a′, b′` chosen after `𝒞, r, ε′` and **before** `ε`, so the time
bound does not depend on `ε`, as printed. The width constants `a, b` come after `𝒞, r, ε` (they are also after
`ε′`, which changes nothing: the output does not depend on `ε′`). The class is the published `MonDepMW.GraphClass`
with `MonDepMW.MonadicallyDependent`, and the bound is claimed for `G ∈ 𝒞`. -/
theorem theorem_6_3 :
    ∃ a₀ b₀ : ℕ, ∃ (P : List Instr) (bw : ℕ), ∀ 𝒞 : MonDepMW.GraphClass, MonDepMW.MonadicallyDependent 𝒞 →
      ∀ r : ℕ, ∀ ε' : ℝ, 0 < ε' → ∃ a' b' : ℕ, ∀ ε : ℚ, 0 < ε → ∃ a b : ℕ,
        ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G ∈ 𝒞 n →
          ∀ W : ℕ, WordSizeOK bw (MonDepMW.graphInput G ++ (r : ℤ) :: ratCode ε) W →
            MonDepMW.RunsWithin P W ⌊(a' : ℝ) * (n : ℝ) ^ (3 + ε') + b'⌋₊
              (MonDepMW.graphInput G ++ (r : ℤ) :: ratCode ε) fun out =>
                ∃ S : List (Finset (Fin n)), Emits out (chainCode S) ∧ IsChain S ∧
                  (S.length : ℝ) ≤ (a₀ : ℝ) * r / (ε : ℝ) + b₀ ∧
                  (chainWidth G S r : ℝ) ≤ (a : ℝ) * (n : ℝ) ^ (ε : ℝ) + b := by sorry

end FOMCMonDep
