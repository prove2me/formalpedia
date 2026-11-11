-- Prove2me | Theorems.Thm_BlockOrthoCSP_Decide_corollary_F_3_2
-- name    : BlockOrthoCSP.Decide.corollary_F_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:14:17.623984+00:00
-- url     : https://prove2.me/theorems/66d438cd-b088-4a95-8ebf-7fbe4d9a405a
-- title:
--   Corollary F.3.2 — singleton purification suffices: $\mathrm{BO}(\mathcal F)$ iff every generated function of arity $\ge 2$ has a block-orthogonal singleton purification
-- statement:
--   Let $q \ge 1$ and let $\mathcal F$ be a finite set of algebraic-valued constraint functions on $D$ with arities $\ge 1$. The joint condition holds exactly when one function at a time suffices:
--   $$\mathrm{BO}(\mathcal F) \iff \forall F \in W_{\mathcal F},\ \operatorname{arity}(F) \ge 2 \Rightarrow F \text{ has a block-orthogonal singleton purification}.$$
--   This is the first reduction of the decision procedure: it lets the arity-compression and certificate arguments work with one generated function at a time.
--
--   Differences from the source:
--   - encoding: D = {0, …, q − 1} → Fin q; reason: the same set
--   - encoding: a finite set F of functions f : D^{r_f} → C (C = algebraic complex numbers), r_f ≥ 1 → F : Finset (CFn q) with IsAlgLanguage F (every arity ≥ 1, every value IsAlgebraic ℚ in ℂ); reason: the paper's field C is the algebraic numbers inside ℂ; absolute values and conjugation are those of ℂ
--   - encoding: a function of arity r ≥ 2 (or k ≥ 2), rows F(x, ∗) indexed by x ∈ D^{r−1} → arity j + 1 with 1 ≤ j; rows indexed by Fin j → Fin q, the column is the last coordinate (Fin.snoc); reason: the same functions; writing r = j + 1 avoids natural-number subtraction
--   - encoding: W_F = {F_I^{[t]} : I a finite #CSP(F) instance, 1 ≤ t ≤ n(I)}, C_I a multiset → W F: instances Inst q t with t ≥ 1 retained variables and h ≥ 0 hidden ones (n = t + h), constraints a List; reason: 1 ≤ t ≤ n is t ≥ 1, h = n − t ≥ 0; the product (F.4) does not depend on the order of the list
--   - reading: Pure(F) computed from one fixed legal generating-set choice (Definition F.2.3) → BO F requires block-orthogonality for every legal generating-set choice (IsJointPurification); reason: Lemma F.3.1 (p. F-10) shows the tested structure does not depend on the choice, so both readings agree
-- source:
--   Liu, Meng, From Block Orthogonality to Decidability in Complex-Weighted Counting CSP, arXiv:2608.14845 (PDF sha256 ad21e5d7…), p. F-13, Corollary F.3.2

import Mathlib
import Definitions.Def_BlockOrthoCSP_Decide_Instance
import Definitions.Def_BlockOrthoCSP_Decide_Conditions

namespace BlockOrthoCSP.Decide

/-- Corollary F.3.2 (singleton purification suffices), p. F-13. -/
theorem corollary_F_3_2 {q : ℕ} (hq : 1 ≤ q) (F : Finset (CFn q)) (hF : IsAlgLanguage F) :
    BO F ↔ SingletonBO F := by sorry

end BlockOrthoCSP.Decide
