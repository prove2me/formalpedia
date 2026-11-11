-- Prove2me | Theorems.Thm_BlockOrthoCSP_Decide_lemma_F_3_4
-- name    : BlockOrthoCSP.Decide.lemma_F_3_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:14:12.338756+00:00
-- url     : https://prove2.me/theorems/5ae059c8-2b8f-4b3b-95e4-0cfbce2bebf2
-- title:
--   Lemma F.3.4 — arity compression: a failure of singleton Block Orthogonality has a witness of arity at most $q^2+1$
-- statement:
--   Let $q \ge 1$ and $\mathcal F$ a finite set of algebraic-valued constraint functions on $D$ with arities $\ge 1$. If the singleton Block Orthogonality condition fails on $W_{\mathcal F}$ (some member of arity $\ge 2$ has no block-orthogonal singleton purification), then it fails for some $H \in W_{\mathcal F}$ with
--   $$2 \le \operatorname{arity}(H) \le q^2 + 1.$$
--   The constant $q^2+1$ counts the at most $q^2$ ordered value pairs of two witnessing rows plus the column variable. This bounds the arities the decision procedure must test.
--
--   Differences from the source:
--   - encoding: D = {0, …, q − 1} → Fin q; reason: the same set
--   - encoding: a finite set F of functions f : D^{r_f} → C (C = algebraic complex numbers), r_f ≥ 1 → F : Finset (CFn q) with IsAlgLanguage F (every arity ≥ 1, every value IsAlgebraic ℚ in ℂ); reason: the paper's field C is the algebraic numbers inside ℂ; absolute values and conjugation are those of ℂ
--   - encoding: a function of arity r ≥ 2 (or k ≥ 2), rows F(x, ∗) indexed by x ∈ D^{r−1} → arity j + 1 with 1 ≤ j; rows indexed by Fin j → Fin q, the column is the last coordinate (Fin.snoc); reason: the same functions; writing r = j + 1 avoids natural-number subtraction
--   - encoding: W_F = {F_I^{[t]} : I a finite #CSP(F) instance, 1 ≤ t ≤ n(I)}, C_I a multiset → W F: instances Inst q t with t ≥ 1 retained variables and h ≥ 0 hidden ones (n = t + h), constraints a List; reason: 1 ≤ t ≤ n is t ≥ 1, h = n − t ≥ 0; the product (F.4) does not depend on the order of the list
--   - reading: the singleton condition 'fails for some function in W_F' → a member of arity ≥ 2 with no block-orthogonal singleton purification (¬ HasBOPurification); reason: the singleton condition only concerns arity ≥ 2 (Corollary F.3.2); by Lemma F.3.1 'no legal singleton purification is block-orthogonal' and 'some is not' agree
-- source:
--   Liu, Meng, From Block Orthogonality to Decidability in Complex-Weighted Counting CSP, arXiv:2608.14845 (PDF sha256 ad21e5d7…), p. F-13, Lemma F.3.4

import Mathlib
import Definitions.Def_BlockOrthoCSP_Decide_Instance
import Definitions.Def_BlockOrthoCSP_Decide_Conditions

namespace BlockOrthoCSP.Decide

/-- Lemma F.3.4 (arity compression), p. F-13. Arity `k = j + 1`. -/
theorem lemma_F_3_4 {q : ℕ} (hq : 1 ≤ q) (F : Finset (CFn q)) (hF : IsAlgLanguage F)
    (hfail : ¬ SingletonBO F) :
    ∃ (j : ℕ) (G : (Fin (j + 1) → Fin q) → ℂ), 1 ≤ j ∧ j + 1 ≤ q ^ 2 + 1 ∧
      (⟨j + 1, G⟩ : CFn q) ∈ W F ∧ ¬ HasBOPurification G := by sorry

end BlockOrthoCSP.Decide
