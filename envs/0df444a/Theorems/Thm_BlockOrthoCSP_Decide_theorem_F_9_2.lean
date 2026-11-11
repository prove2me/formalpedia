-- Prove2me | Theorems.Thm_BlockOrthoCSP_Decide_theorem_F_9_2
-- name    : BlockOrthoCSP.Decide.theorem_F_9_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:14:33.009633+00:00
-- url     : https://prove2.me/theorems/02f4c164-02fd-4238-a3ad-f7813912f0af
-- title:
--   Theorem F.9.2 — structural collapse: $\mathrm{BO}$ implies $\mathrm{TP}$ and $\mathrm{Mal}$ with one common operation, hence $\mathrm{CC} \iff \mathrm{BO}$
-- statement:
--   For every $q \ge 1$ and every finite set $\mathcal F$ of algebraic-valued constraint functions on $D$,
--   $$\mathrm{BO}(\mathcal F) \Rightarrow \mathrm{TP}(\mathcal F) \wedge \mathrm{Mal}(\mathcal F).$$
--   More explicitly, under $\mathrm{BO}(\mathcal F)$ there is one Mal'tsev operation $\varphi : D^3 \to D$ such that for every $F \in W_{\mathcal F}$, $\varphi$ preserves $\Phi_F$, and if $\operatorname{arity}(F) \ge 2$ it preserves $\Omega_F$. Consequently $\mathrm{CC}(\mathcal F) \iff \mathrm{BO}(\mathcal F)$. All three statements are conjuncts of the Lean theorem.
--
--   Differences from the source:
--   - encoding: D = {0, …, q − 1} → Fin q; reason: the same set
--   - encoding: a finite set F of functions f : D^{r_f} → C (C = algebraic complex numbers), r_f ≥ 1 → F : Finset (CFn q) with IsAlgLanguage F (every arity ≥ 1, every value IsAlgebraic ℚ in ℂ); reason: the paper's field C is the algebraic numbers inside ℂ; absolute values and conjugation are those of ℂ
--   - encoding: a function of arity r ≥ 2 (or k ≥ 2), rows F(x, ∗) indexed by x ∈ D^{r−1} → arity j + 1 with 1 ≤ j; rows indexed by Fin j → Fin q, the column is the last coordinate (Fin.snoc); reason: the same functions; writing r = j + 1 avoids natural-number subtraction
--   - encoding: W_F = {F_I^{[t]} : I a finite #CSP(F) instance, 1 ≤ t ≤ n(I)}, C_I a multiset → W F: instances Inst q t with t ≥ 1 retained variables and h ≥ 0 hidden ones (n = t + h), constraints a List; reason: 1 ≤ t ≤ n is t ≥ 1, h = n − t ≥ 0; the product (F.4) does not depend on the order of the list
--   - reading: Pure(F) computed from one fixed legal generating-set choice (Definition F.2.3) → BO F requires block-orthogonality for every legal generating-set choice (IsJointPurification); reason: Lemma F.3.1 (p. F-10) shows the tested structure does not depend on the choice, so both readings agree
-- source:
--   Liu, Meng, From Block Orthogonality to Decidability in Complex-Weighted Counting CSP, arXiv:2608.14845 (PDF sha256 ad21e5d7…), p. F-39, Theorem F.9.2

import Mathlib
import Definitions.Def_ConsModCount_Polymorphism
import Definitions.Def_BlockOrthoCSP_Decide_Instance
import Definitions.Def_BlockOrthoCSP_Decide_Rows
import Definitions.Def_BlockOrthoCSP_Decide_Conditions

namespace BlockOrthoCSP.Decide

/-- Theorem F.9.2 (structural collapse), p. F-39: `BO(F) ⟹ TP(F) ∧ Mal(F)`; explicitly, one
Mal'tsev `φ` preserves `Φ_F` for every `F ∈ W_F` and `Ω_F` for every `F ∈ W_F` of arity `≥ 2`;
consequently `CC(F) ⟺ BO(F)`. -/
theorem theorem_F_9_2 {q : ℕ} (hq : 1 ≤ q) (F : Finset (CFn q)) (hF : IsAlgLanguage F) :
    (BO F → TP F ∧ Mal F) ∧
    (BO F → ∃ φ : Fin q → Fin q → Fin q → Fin q, ConsModCount.IsMaltsev φ ∧
      ∀ G ∈ W F, ConsModCount.Preserves (ConsModCount.ternary φ) (Phi G.2) ∧
        ∀ (j : ℕ) (G' : (Fin (j + 1) → Fin q) → ℂ), 1 ≤ j → G = ⟨j + 1, G'⟩ →
          ConsModCount.Preserves (ConsModCount.ternary φ) (Omega G')) ∧
    (CC F ↔ BO F) := by sorry

end BlockOrthoCSP.Decide
