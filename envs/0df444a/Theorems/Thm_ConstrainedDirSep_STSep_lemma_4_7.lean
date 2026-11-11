-- Prove2me | Theorems.Thm_ConstrainedDirSep_STSep_lemma_4_7
-- name    : ConstrainedDirSep.STSep.lemma_4_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:08:58.2132+00:00
-- url     : https://prove2.me/theorems/f9605aea-195d-4048-ab60-a11b13f8011c
-- title:
--   Lemma 4.7 — minimum unary cost over min–max closed binary CSPs in polynomial time
-- statement:
--   Consider binary CSPs whose variables $X_1,\dots,X_r$ have domains $[d_i]$, arbitrary unary allowed sets $U_i\subseteq[d_i]$, and binary relations $R_{ij}$ ($i\ne j$) each closed under both coordinatewise minimum and coordinatewise maximum, together with a nonnegative integer cost $\omega_i(p)$ for every domain value. There are a constant $C$ and a deterministic multi-stack Turing machine $M$ such that, on the encoding (length $L$) of every such instance with its binary costs, $M$ halts within $C(L+1)^C$ steps and outputs either "none", when no satisfying assignment exists, or a satisfying assignment $x$ minimizing
--   $$\sum_{i}\omega_i(x_i)$$
--   over all satisfying assignments.
--
--   This is the weighted step of each branch of Theorem 4.8; the paper cites it from Cohen, Cooper, Jeavons and Krokhin (2004).
--
--   Differences from the source:
--   - reading: "polynomial time" for an unnamed machine model → a deterministic Mathlib multi-stack Turing machine (TM2) within C·(L+1)^C steps on the input word of length L (costs in binary), one universal constant C; reason: the paper fixes no model, and polynomial time is the same in all polynomially equivalent deterministic models.
--   - reading: a binary CSP with arbitrary binary constraints → one relation R_ij per ordered pair i ≠ j, given by its membership bits over [d_i] × [d_j]; reason: constraints on one pair intersect, a reversed pair transposes, an absent constraint is the full relation, and all preserve min–max closure; the conversion is polynomial.
-- source:
--   Olkowski, Ramanujan, Constrained Directed Separation: Algorithms and Classifications, STOC 2027 submission (manuscript sha256 4dd06c29…), p. 17 (PDF 20), Lemma 4.7 (proof sketch p. 42, PDF 45), cited from [CCJK04, Lemma 4.5 and Corollary 3.6]

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_ConstrainedDirSep_STSep_Encoding
import Definitions.Def_ConstrainedDirSep_STSep_Quadrant
import Definitions.Def_ConstrainedDirSep_STSep_ChainCSP
import Definitions.Def_ConstrainedDirSep_STSep_BinaryCSP

namespace ConstrainedDirSep.STSep

/-- Olkowski, Ramanujan, *Constrained Directed Separation*, STOC 2027 submission (manuscript
sha256 4dd06c29…), p. 17 (PDF 20), Lemma 4.7 (Unary optimization over min–max closed constraints
[CCJK04]): for a binary CSP with domains `[d_i]`, arbitrary unary allowed sets and binary relations
closed under coordinatewise minimum and maximum, and nonnegative integer costs `ω_i(p)`, a
minimum-cost satisfying assignment, or the conclusion that none exists, is found in polynomial
time. -/
theorem lemma_4_7 :
    ∃ C : ℕ, ∃ M : Turing.TM2ComputableAux Bool Bool,
      ∀ I : BinaryCSP, I.WF → (∀ i j, i ≠ j → MinMaxClosed (I.R i j : Set (ℕ × ℕ))) →
        ∀ ω : Fin I.r → ℕ → ℕ,
        ∃ out : List Bool,
          HMBinPacking.OutputsWithin M (encWBinaryCSP I ω) out
            (C * ((encWBinaryCSP I ω).length + 1) ^ C) ∧
          ((out = encNone ∧ ∀ x, ¬ I.Satisfies x) ∨
            ∃ x : Fin I.r → ℕ, out = encAssign x ∧ I.Satisfies x ∧
              ∀ y : Fin I.r → ℕ, I.Satisfies y → assignCost ω x ≤ assignCost ω y) := by sorry

end ConstrainedDirSep.STSep
