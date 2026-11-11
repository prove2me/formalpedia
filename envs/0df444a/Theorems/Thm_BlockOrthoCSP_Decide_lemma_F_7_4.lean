-- Prove2me | Theorems.Thm_BlockOrthoCSP_Decide_lemma_F_7_4
-- name    : BlockOrthoCSP.Decide.lemma_F_7_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:13:54.386025+00:00
-- url     : https://prove2.me/theorems/de9329a4-485d-451b-821c-0f4865af179a
-- title:
--   Lemma F.7.4 — under $\mathrm{BO}(\mathcal F)$ every finite family of generated support relations has a common Mal'tsev polymorphism
-- statement:
--   Let $q \ge 1$ and $\mathcal F$ a finite set of algebraic-valued constraint functions on $D$ with $\mathrm{BO}(\mathcal F)$. For every finite family $F_1,\dots,F_N \in W_{\mathcal F}$ there is a Mal'tsev operation $\varphi : D^3 \to D$ preserving every support $\Phi_{F_1},\dots,\Phi_{F_N}$.
--
--   Differences from the source:
--   - encoding: D = {0, …, q − 1} → Fin q; reason: the same set
--   - encoding: a finite set F of functions f : D^{r_f} → C (C = algebraic complex numbers), r_f ≥ 1 → F : Finset (CFn q) with IsAlgLanguage F (every arity ≥ 1, every value IsAlgebraic ℚ in ℂ); reason: the paper's field C is the algebraic numbers inside ℂ; absolute values and conjugation are those of ℂ
--   - encoding: W_F = {F_I^{[t]} : I a finite #CSP(F) instance, 1 ≤ t ≤ n(I)}, C_I a multiset → W F: instances Inst q t with t ≥ 1 retained variables and h ≥ 0 hidden ones (n = t + h), constraints a List; reason: 1 ≤ t ≤ n is t ≥ 1, h = n − t ≥ 0; the product (F.4) does not depend on the order of the list
--   - reading: Pure(F) computed from one fixed legal generating-set choice (Definition F.2.3) → BO F requires block-orthogonality for every legal generating-set choice (IsJointPurification); reason: Lemma F.3.1 (p. F-10) shows the tested structure does not depend on the choice, so both readings agree
--   - encoding: a finite family of generated support relations → Φ of each member of a family Gs : Fin N → CFn q of members of W_F; reason: every finite family can be indexed by Fin N
-- source:
--   Liu, Meng, From Block Orthogonality to Decidability in Complex-Weighted Counting CSP, arXiv:2608.14845 (PDF sha256 ad21e5d7…), p. F-31, Lemma F.7.4

import Mathlib
import Definitions.Def_ConsModCount_Polymorphism
import Definitions.Def_BlockOrthoCSP_Decide_Instance
import Definitions.Def_BlockOrthoCSP_Decide_Rows
import Definitions.Def_BlockOrthoCSP_Decide_Conditions

namespace BlockOrthoCSP.Decide

/-- Lemma F.7.4, p. F-31: under `BO(F)`, every finite family `Φ_{G_1}, …, Φ_{G_N}` of generated
support relations has a common Mal'tsev polymorphism. -/
theorem lemma_F_7_4 {q : ℕ} (hq : 1 ≤ q) (F : Finset (CFn q)) (hF : IsAlgLanguage F)
    (hBO : BO F) (N : ℕ) (Gs : Fin N → CFn q) (hGs : ∀ i, Gs i ∈ W F) :
    ∃ φ : Fin q → Fin q → Fin q → Fin q, ConsModCount.IsMaltsev φ ∧
      ∀ i, ConsModCount.Preserves (ConsModCount.ternary φ) (Phi (Gs i).2) := by sorry

end BlockOrthoCSP.Decide
