-- Prove2me | Theorems.Thm_BlockOrthoCSP_Decide_theorem_F_6_2
-- name    : BlockOrthoCSP.Decide.theorem_F_6_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:14:03.345579+00:00
-- url     : https://prove2.me/theorems/3d428a64-a848-446e-9756-a61044899cef
-- title:
--   Theorem F.6.2 — exact decision of global Block Orthogonality: $\mathrm{BO}(\mathcal F)$ is decidable
-- statement:
--   Procedure F.6.1 is a total exact algorithm that, on input $q \ge 1$ and a finite set $\mathcal F$ of algebraic-valued constraint functions on $D$, returns yes if and only if $\mathrm{BO}(\mathcal F)$ holds. Stated as: there is one computable function on exact input codes which, on every valid code, returns true exactly when $\mathrm{BO}$ holds for the decoded input,
--   $$\exists\, \mathrm{dec}\ \text{computable},\ \forall c \text{ valid},\ \mathrm{dec}(c) = \mathrm{true} \iff \mathrm{BO}(\mathrm{decode}(c)).$$
--
--   Differences from the source:
--   - encoding: D = {0, …, q − 1} → Fin q; reason: the same set
--   - encoding: a finite set F of functions f : D^{r_f} → C (C = algebraic complex numbers), r_f ≥ 1 → F : Finset (CFn q) with IsAlgLanguage F (every arity ≥ 1, every value IsAlgebraic ℚ in ℂ); reason: the paper's field C is the algebraic numbers inside ℂ; absolute values and conjugation are those of ℂ
--   - encoding: W_F = {F_I^{[t]} : I a finite #CSP(F) instance, 1 ≤ t ≤ n(I)}, C_I a multiset → W F: instances Inst q t with t ≥ 1 retained variables and h ≥ 0 hidden ones (n = t + h), constraints a List; reason: 1 ≤ t ≤ n is t ≥ 1, h = n − t ≥ 0; the product (F.4) does not depend on the order of the list
--   - reading: Pure(F) computed from one fixed legal generating-set choice (Definition F.2.3) → BO F requires block-orthogonality for every legal generating-set choice (IsJointPurification); reason: Lemma F.3.1 (p. F-10) shows the tested structure does not depend on the choice, so both readings agree
--   - encoding: exact input (q, F): 'standard exact representations specifying the chosen complex root' [Coh93] → LangCode = (q, list of (r, list of q^r AlgCode values in lexicographic order of D^r)); an AlgCode is a nonzero integer polynomial with a closed rational box isolating exactly one root (LangCode.Valid); decodeLang identifies duplicate functions; reason: one standard exact representation; every algebraic number has such a code, so every admissible (q, F) is decoded from a valid code; invalid codes may get any answer
--   - encoding: there is a (total, exact) algorithm → ∃ a function on codes with Mathlib's Computable, correct on every valid input; reason: Mathlib computability (partial recursive functions over Primcodable codes) is the meaning of 'algorithm'; a total computable function halts on every input
--   - reading: 'Procedure F.6.1 is a total exact algorithm that returns yes iff BO(F)' → existence of a computable total decider for BO on valid codes; reason: implementing Procedure F.6.1 itself as a Lean definition is out of scope; the procedure is the paper's witness for the existential
-- source:
--   Liu, Meng, From Block Orthogonality to Decidability in Complex-Weighted Counting CSP, arXiv:2608.14845 (PDF sha256 ad21e5d7…), p. F-28, Theorem F.6.2 (Procedure F.6.1, pp. F-27–F-28)

import Mathlib
import Definitions.Def_BlockOrthoCSP_Decide_Conditions
import Definitions.Def_BlockOrthoCSP_Decide_Codes

namespace BlockOrthoCSP.Decide

/-- Theorem F.6.2 (exact decision of global BO), p. F-28: a computable, total decider on exact
input codes returns `true` exactly when `BO(F)` holds for the decoded input. -/
theorem theorem_F_6_2 :
    ∃ dec : LangCode → Bool, Computable dec ∧
      ∀ c : LangCode, c.Valid → (dec c = true ↔ BO (decodeLang c)) := by sorry

end BlockOrthoCSP.Decide
