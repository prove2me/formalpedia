-- Prove2me | Theorems.Thm_BlockOrthoCSP_Decide_theorem_F_5_8
-- name    : BlockOrthoCSP.Decide.theorem_F_5_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:13:22.024716+00:00
-- url     : https://prove2.me/theorems/9581f9e7-f9c1-4678-8074-97b32f5738cc
-- title:
--   Theorem F.5.8 — universal identity oracle: $P(z_I, \overline{z_I}) = 0$ for all labelled instances is decidable
-- statement:
--   Fix $q \ge 1$, a finite set $\mathcal F$ of algebraic-valued constraint functions on $D$ and $k \ge 1$. For a polynomial $P \in \mathbb C[X_a, Y_a : a \in D^k]$ in $2q^k$ independent variables with exactly coded algebraic coefficients, and a $k$-labelled $\mathcal F$-instance $I$, write $P(z_I, \overline{z_I})$ for the substitution $X_a = z_I(a)$, $Y_a = \overline{z_I(a)}$. There is a total exact algorithm deciding whether
--   $$P(z_I, \overline{z_I}) = 0 \quad \text{for every } I \in \mathfrak M_k. \qquad (F.40)$$
--   In Lean: one computable function of the input code of $(q,\mathcal F)$, of $k$ and of the polynomial code, correct on all valid codes.
--
--   Differences from the source:
--   - encoding: D = {0, …, q − 1} → Fin q; reason: the same set
--   - encoding: a finite set F of functions f : D^{r_f} → C (C = algebraic complex numbers), r_f ≥ 1 → F : Finset (CFn q) with IsAlgLanguage F (every arity ≥ 1, every value IsAlgebraic ℚ in ℂ); reason: the paper's field C is the algebraic numbers inside ℂ; absolute values and conjugation are those of ℂ
--   - encoding: there is a (total, exact) algorithm → ∃ a function on codes with Mathlib's Computable, correct on every valid input; reason: Mathlib computability (partial recursive functions over Primcodable codes) is the meaning of 'algorithm'; a total computable function halts on every input
--   - encoding: exact input (q, F): 'standard exact representations specifying the chosen complex root' [Coh93] → LangCode = (q, list of (r, list of q^r AlgCode values in lexicographic order of D^r)); an AlgCode is a nonzero integer polynomial with a closed rational box isolating exactly one root (LangCode.Valid); decodeLang identifies duplicate functions; reason: one standard exact representation; every algebraic number has such a code, so every admissible (q, F) is decoded from a valid code; invalid codes may get any answer
--   - generalization: 'Fix k ≥ 1' (and the standing F): an algorithm with input P → one computable decider whose input is (code of (q, F), k, code of P); reason: uniform in (q, F, k); fixing the first two inputs gives the paper's algorithm for fixed F and k, and Procedure F.6.1 uses it this way
--   - encoding: I ∈ M_k (label-preserving isomorphism classes of k-labelled instances) → every k-labelled instance Inst q k over F (variables Fin (k + h), the first k labelled), z_I = I.genFn; reason: P(z_I, conj z_I) only depends on the class; isolated unlabelled variables, repeated constraints and repeated scope indices are all allowed
--   - encoding: P given as a finite list of monomials with exactly encoded algebraic-complex coefficients → PolyCode (Bool × List ℕ): coefficient AlgCodes, (false, a) for X_a and (true, a) for Y_a; valid codes only; reason: the paper's input format
-- source:
--   Liu, Meng, From Block Orthogonality to Decidability in Complex-Weighted Counting CSP, arXiv:2608.14845 (PDF sha256 ad21e5d7…), p. F-27, Theorem F.5.8

import Mathlib
import Definitions.Def_BlockOrthoCSP_Decide_Instance
import Definitions.Def_BlockOrthoCSP_Decide_Codes

namespace BlockOrthoCSP.Decide

open ComplexConjugate

/-- Theorem F.5.8 (universal identity oracle), p. F-27: a computable test, on the exact input
`(q, F)`, `k ≥ 1` and an exactly coded polynomial `P ∈ ℂ[X_a, Y_a : a ∈ D^k]`, of whether
`P(z_I, conj z_I) = 0` for every `k`-labelled `F`-instance `I`. -/
theorem theorem_F_5_8 :
    ∃ dec : LangCode × ℕ × PolyCode (Bool × List ℕ) → Bool, Computable dec ∧
      ∀ c : LangCode, c.Valid → ∀ k : ℕ, 1 ≤ k →
        ∀ P : PolyCode (Bool × List ℕ), P.Valid (decodeXY c.1 k) →
          (dec (c, k, P) = true ↔
            ∀ I : Inst c.1 k, I.Over (decodeLang c) →
              MvPolynomial.eval (Sum.elim I.genFn (fun a => conj (I.genFn a)))
                (P.decode (decodeXY c.1 k)) = 0) := by sorry

end BlockOrthoCSP.Decide
