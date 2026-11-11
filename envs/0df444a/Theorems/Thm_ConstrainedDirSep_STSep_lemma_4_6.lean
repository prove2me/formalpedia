-- Prove2me | Theorems.Thm_ConstrainedDirSep_STSep_lemma_4_6
-- name    : ConstrainedDirSep.STSep.lemma_4_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:08:50.443173+00:00
-- url     : https://prove2.me/theorems/958c8d6a-4d5a-4fd4-9d6b-222e1f9d904f
-- title:
--   Lemma 4.6 — arc consistency decides min-closed binary CSPs in polynomial time
-- statement:
--   Consider binary CSPs whose variables $X_1,\dots,X_r$ have finite linearly ordered domains $[d_i]$, arbitrary unary allowed sets $U_i\subseteq[d_i]$, and binary relations $R_{ij}$ ($i\ne j$), each closed under coordinatewise minimum. Then:
--
--   1. **Arc consistency decides feasibility:** the instance has a satisfying assignment if and only if every domain left by enforcing arc consistency (the greatest arc-consistent family of domains) is nonempty;
--   2. this runs in **polynomial time and returns a satisfying assignment whenever one exists:** there are a constant $C$ and a deterministic multi-stack Turing machine $M$ such that on the encoding of every such instance, of length $L$, $M$ halts within $C(L+1)^C$ steps and outputs either "none", when no satisfying assignment exists, or a satisfying assignment.
--
--   This is the feasibility step of each branch in Theorem 4.8; the paper cites it from Jeavons and Cooper (1995).
--
--   Differences from the source:
--   - reading: "polynomial time" for an unnamed machine model → a deterministic Mathlib multi-stack Turing machine (TM2) within C·(L+1)^C steps on the input word of length L, one universal constant C; reason: the paper fixes no model, and polynomial time is the same in all polynomially equivalent deterministic models.
--   - reading: a binary CSP with arbitrary binary constraints → one relation R_ij per ordered pair i ≠ j, given by its membership bits over [d_i] × [d_j], domains written out explicitly; reason: constraints on one pair intersect, a reversed pair transposes, an absent constraint is the full relation, and all preserve min-closure; the conversion is polynomial.
--   - encoding: finite linearly ordered domains → [d_i] = {1, …, d_i}; reason: every finite linear order is isomorphic to one of these.
--   - reading: "arc consistency decides feasibility in polynomial time" → (a) a satisfying assignment exists iff every domain of the greatest arc-consistent family is nonempty, and (b) a polynomial-time machine outputs a satisfying assignment or "none"; reason: enforcing arc consistency deletes exactly the values lying in no arc-consistent family, so its result is the greatest one, and the machine is not constrained to a particular procedure.
-- source:
--   Olkowski, Ramanujan, Constrained Directed Separation: Algorithms and Classifications, STOC 2027 submission (manuscript sha256 4dd06c29…), p. 16 (PDF 19), Lemma 4.6 (proof p. 41–42, PDF 44–45), cited from [JC95, Section 4]

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_ConstrainedDirSep_STSep_Encoding
import Definitions.Def_ConstrainedDirSep_STSep_Quadrant
import Definitions.Def_ConstrainedDirSep_STSep_ChainCSP
import Definitions.Def_ConstrainedDirSep_STSep_BinaryCSP

namespace ConstrainedDirSep.STSep

/-- Olkowski, Ramanujan, *Constrained Directed Separation*, STOC 2027 submission (manuscript
sha256 4dd06c29…), p. 16 (PDF 19), Lemma 4.6 (Min-closed feasibility [JC95, Section 4]). -/
theorem lemma_4_6 :
    ∃ C : ℕ, ∃ M : Turing.TM2ComputableAux Bool Bool,
      ∀ I : BinaryCSP, I.WF → (∀ i j, i ≠ j → MinClosed (I.R i j : Set (ℕ × ℕ))) →
        ((∃ x, I.Satisfies x) ↔ ∀ i, (I.acClosure i).Nonempty) ∧
        ∃ out : List Bool,
          HMBinPacking.OutputsWithin M (encBinaryCSP I) out
            (C * ((encBinaryCSP I).length + 1) ^ C) ∧
          ((out = encNone ∧ ∀ x, ¬ I.Satisfies x) ∨
            ∃ x : Fin I.r → ℕ, out = encAssign x ∧ I.Satisfies x) := by sorry

end ConstrainedDirSep.STSep
