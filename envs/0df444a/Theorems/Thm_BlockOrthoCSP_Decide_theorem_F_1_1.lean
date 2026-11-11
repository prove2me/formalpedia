-- Prove2me | Theorems.Thm_BlockOrthoCSP_Decide_theorem_F_1_1
-- name    : BlockOrthoCSP.Decide.theorem_F_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:14:16.459337+00:00
-- url     : https://prove2.me/theorems/e4572026-dc02-4d03-a573-1c21b400eda0
-- title:
--   Theorem F.1.1 — uniform decidability: Cai and Chen's tractability criterion $\mathrm{CC}(\mathcal F)$ is decidable, and $\mathrm{CC}(\mathcal F) \iff \mathrm{BO}(\mathcal F)$
-- statement:
--   Let $D = \{0,\dots,q-1\}$. For a finite set $\mathcal F$ of algebraic complex-valued constraint functions on $D$, Cai and Chen's criterion is $\mathrm{CC}(\mathcal F) = \mathrm{BO}(\mathcal F) \wedge \mathrm{TP}(\mathcal F) \wedge \mathrm{Mal}(\mathcal F)$, three conditions on the infinite generated family $W_{\mathcal F}$. The theorem has two clauses, stated together:
--
--   (a) There is a deterministic algorithm that, given $q \ge 1$ and $\mathcal F$, halts and decides whether $\mathrm{CC}(\mathcal F)$ holds: one computable function on exact input codes which, on every valid code, returns true exactly when $\mathrm{CC}$ holds for the decoded input.
--
--   (b) For every $q \ge 1$ and every such $\mathcal F$,
--   $$\mathrm{CC}(\mathcal F) \iff \mathrm{BO}(\mathcal F). \qquad (F.2)$$
--
--   This answers Cai and Chen's question [CC17, §9] whether their criterion can be decided from the finite set $\mathcal F$ alone. $q = 1$ and $\mathcal F = \emptyset$ are included.
--
--   Differences from the source:
--   - encoding: D = {0, …, q − 1} → Fin q; reason: the same set
--   - encoding: a finite set F of functions f : D^{r_f} → C (C = algebraic complex numbers), r_f ≥ 1 → F : Finset (CFn q) with IsAlgLanguage F (every arity ≥ 1, every value IsAlgebraic ℚ in ℂ); reason: the paper's field C is the algebraic numbers inside ℂ; absolute values and conjugation are those of ℂ
--   - encoding: W_F = {F_I^{[t]} : I a finite #CSP(F) instance, 1 ≤ t ≤ n(I)}, C_I a multiset → W F: instances Inst q t with t ≥ 1 retained variables and h ≥ 0 hidden ones (n = t + h), constraints a List; reason: 1 ≤ t ≤ n is t ≥ 1, h = n − t ≥ 0; the product (F.4) does not depend on the order of the list
--   - reading: Pure(F) computed from one fixed legal generating-set choice (Definition F.2.3) → BO F requires block-orthogonality for every legal generating-set choice (IsJointPurification); reason: Lemma F.3.1 (p. F-10) shows the tested structure does not depend on the choice, so both readings agree
--   - encoding: exact input (q, F): 'standard exact representations specifying the chosen complex root' [Coh93] → LangCode = (q, list of (r, list of q^r AlgCode values in lexicographic order of D^r)); an AlgCode is a nonzero integer polynomial with a closed rational box isolating exactly one root (LangCode.Valid); decodeLang identifies duplicate functions; reason: one standard exact representation; every algebraic number has such a code, so every admissible (q, F) is decoded from a valid code; invalid codes may get any answer
--   - encoding: there is a (total, exact) algorithm → ∃ a function on codes with Mathlib's Computable, correct on every valid input; reason: Mathlib computability (partial recursive functions over Primcodable codes) is the meaning of 'algorithm'; a total computable function halts on every input
-- source:
--   Liu, Meng, From Block Orthogonality to Decidability in Complex-Weighted Counting CSP, arXiv:2608.14845 (PDF sha256 ad21e5d7…), p. F-1, Theorem F.1.1 (= Theorem 1.1, p. 1); proof §F.9.1, p. F-39

import Mathlib
import Definitions.Def_BlockOrthoCSP_Decide_Instance
import Definitions.Def_BlockOrthoCSP_Decide_Conditions
import Definitions.Def_BlockOrthoCSP_Decide_Codes

namespace BlockOrthoCSP.Decide

/-- Theorem F.1.1 (uniform decidability), p. F-1: (a) one computable total decider on exact input
codes `(q, F)` returns `true` exactly when `CC(F)` holds for the decoded input; (b) for every
`q ≥ 1` and every finite set `F` of algebraic-valued constraint functions, `CC(F) ⟺ BO(F)`. -/
theorem theorem_F_1_1 :
    (∃ dec : LangCode → Bool, Computable dec ∧
      ∀ c : LangCode, c.Valid → (dec c = true ↔ CC (decodeLang c))) ∧
    ∀ (q : ℕ), 1 ≤ q → ∀ F : Finset (CFn q), IsAlgLanguage F → (CC F ↔ BO F) := by sorry

end BlockOrthoCSP.Decide
