-- Prove2me | Theorems.Thm_BlockOrthoCSP_Decide_theorem_F_8_4
-- name    : BlockOrthoCSP.Decide.theorem_F_8_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:15:27.675358+00:00
-- url     : https://prove2.me/theorems/63f2a168-f5a9-4ef4-86f9-ec6792af1861
-- title:
--   Theorem F.8.4 — under $\mathrm{BO}(\mathcal F)$ the row-equivalence detector $C_n$, $n = 1+tL_q$, is generated and has support $\Omega_F$; $t$ and an instance for $C_n$ are computable
-- statement:
--   Assume $\mathrm{BO}(\mathcal F)$ for a finite set $\mathcal F$ of algebraic-valued constraint functions on $D$, $q \ge 1$. Let $F : D^r \to K$, $r \ge 2$, be any member of $W_{\mathcal F}$. There is an integer $t \ge 0$ such that, for $n = 1 + tL_q$, the $2(r-1)$-ary function
--   $$C_n(x,y) = \sum_{z\in D} F(x,z)^{(e_K-1)n}\,F(y,z)^n \qquad (F.54)$$
--   belongs to $W_{\mathcal F}$ and $\Phi_{C_n} = \Omega_F$ (F.55). Moreover, an algorithm computes, from the exact values and an instance $I$ with $F = F_I^{[r]}$, such $t$ (hence $n$) and an instance $J$ with $C_n = F_J^{[2(r-1)]}$, retained variables ordered $(x, y)$.
--
--   Differences from the source:
--   - encoding: D = {0, …, q − 1} → Fin q; reason: the same set
--   - encoding: a finite set F of functions f : D^{r_f} → C (C = algebraic complex numbers), r_f ≥ 1 → F : Finset (CFn q) with IsAlgLanguage F (every arity ≥ 1, every value IsAlgebraic ℚ in ℂ); reason: the paper's field C is the algebraic numbers inside ℂ; absolute values and conjugation are those of ℂ
--   - encoding: a function of arity r ≥ 2 (or k ≥ 2), rows F(x, ∗) indexed by x ∈ D^{r−1} → arity j + 1 with 1 ≤ j; rows indexed by Fin j → Fin q, the column is the last coordinate (Fin.snoc); reason: the same functions; writing r = j + 1 avoids natural-number subtraction
--   - encoding: W_F = {F_I^{[t]} : I a finite #CSP(F) instance, 1 ≤ t ≤ n(I)}, C_I a multiset → W F: instances Inst q t with t ≥ 1 retained variables and h ≥ 0 hidden ones (n = t + h), constraints a List; reason: 1 ≤ t ≤ n is t ≥ 1, h = n − t ≥ 0; the product (F.4) does not depend on the order of the list
--   - reading: Pure(F) computed from one fixed legal generating-set choice (Definition F.2.3) → BO F requires block-orthogonality for every legal generating-set choice (IsJointPurification); reason: Lemma F.3.1 (p. F-10) shows the tested structure does not depend on the choice, so both readings agree
--   - encoding: there is a (total, exact) algorithm → ∃ a function on codes with Mathlib's Computable, correct on every valid input; reason: Mathlib computability (partial recursive functions over Primcodable codes) is the meaning of 'algorithm'; a total computable function halts on every input
--   - encoding: exact input (q, F): 'standard exact representations specifying the chosen complex root' [Coh93] → LangCode = (q, list of (r, list of q^r AlgCode values in lexicographic order of D^r)); an AlgCode is a nonzero integer polynomial with a closed rational box isolating exactly one root (LangCode.Valid); decodeLang identifies duplicate functions; reason: one standard exact representation; every algebraic number has such a code, so every admissible (q, F) is decoded from a valid code; invalid codes may get any answer
--   - encoding: F : D^r → K → a member ⟨j+1, G⟩ of W F with G : (Fin (j+1) → Fin q) → ℂ; reason: every member of W_F is K-valued (p. F-14), so nothing is lost
--   - encoding: 'given the exact values of F and an instance I with F = F_I^{[r]}, computes such integers t, n and an instance J' → a computable map (input code, r, code of I) ↦ (t, code of J), required to be correct whenever the input code is valid, BO holds for the decoded input and the code of I decodes; n = 1 + t L_q is determined by t; reason: the input code carries the exact values the instance refers to
-- source:
--   Liu, Meng, From Block Orthogonality to Decidability in Complex-Weighted Counting CSP, arXiv:2608.14845 (PDF sha256 ad21e5d7…), p. F-36, Theorem F.8.4

import Mathlib
import Definitions.Def_BlockOrthoCSP_Decide_Instance
import Definitions.Def_BlockOrthoCSP_Decide_Rows
import Definitions.Def_BlockOrthoCSP_Decide_Conditions
import Definitions.Def_BlockOrthoCSP_Decide_Codes
import Definitions.Def_BlockOrthoCSP_Decide_Realization

namespace BlockOrthoCSP.Decide

/-- Theorem F.8.4 (row-equivalence realization), p. F-36, for `r = j + 1 ≥ 2`: under `BO(F)`
some `t ≥ 0` makes `C_n` (`n = 1 + t L_q`, see `detector`) a member of `W_F` with
`Φ_{C_n} = Ω_F`; and `t` together with an instance `J` with `C_n = F_J^{[2(r−1)]}` (retained
variables ordered `(x, y)`) is computable from the exact input and an instance `I` with
`F = F_I^{[r]}`. -/
theorem theorem_F_8_4 :
    (∀ (q : ℕ), 1 ≤ q → ∀ F : Finset (CFn q), IsAlgLanguage F → BO F →
      ∀ (j : ℕ) (G : (Fin (j + 1) → Fin q) → ℂ), 1 ≤ j → (⟨j + 1, G⟩ : CFn q) ∈ W F →
        ∃ t : ℕ, (⟨j + j, detector F t G⟩ : CFn q) ∈ W F ∧ Phi (detector F t G) = Omega G) ∧
    ∃ alg : LangCode × ℕ × InstCode → ℕ × InstCode, Computable alg ∧
      ∀ c : LangCode, c.Valid → BO (decodeLang c) →
        ∀ j : ℕ, 1 ≤ j → ∀ (cI : InstCode) (I : Inst c.1 (j + 1)),
          decodeInst c (j + 1) cI = some I →
            ∃ J : Inst c.1 (j + j), decodeInst c (j + j) (alg (c, j + 1, cI)).2 = some J ∧
              J.genFn = detector (decodeLang c) (alg (c, j + 1, cI)).1 I.genFn ∧
              Phi (detector (decodeLang c) (alg (c, j + 1, cI)).1 I.genFn) = Omega I.genFn := by sorry

end BlockOrthoCSP.Decide
