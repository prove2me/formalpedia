-- Prove2me | Theorems.Thm_BlockOrthoCSP_Decide_lemma_F_9_1
-- name    : BlockOrthoCSP.Decide.lemma_F_9_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:13:14.861622+00:00
-- url     : https://prove2.me/theorems/27de8775-a9e1-465d-81c3-b06aae04584f
-- title:
--   Lemma F.9.1 — a Mal'tsev polymorphism of $\Omega_F$ makes the type map of $F$ a type-partition map
-- statement:
--   Let $q \ge 1$, $F : D^r \to \mathbb C$ with algebraic values and $r \ge 2$, and let $\varphi : D^3 \to D$ be a Mal'tsev operation preserving the row-equivalence relation $\Omega_F$. Then the type map of $F$ is a type-partition map: for every $0 \le \ell \le r-1$ and $\alpha, \beta \in D^\ell$,
--   $$\mathrm{type}_F(\alpha) = \mathrm{type}_F(\beta) \quad\text{or}\quad \mathrm{type}_F(\alpha)\cap\mathrm{type}_F(\beta) = \emptyset.$$
--
--   Differences from the source:
--   - encoding: D = {0, …, q − 1} → Fin q; reason: the same set
--   - encoding: a function of arity r ≥ 2 (or k ≥ 2), rows F(x, ∗) indexed by x ∈ D^{r−1} → arity j + 1 with 1 ≤ j; rows indexed by Fin j → Fin q, the column is the last coordinate (Fin.snoc); reason: the same functions; writing r = j + 1 avoids natural-number subtraction
--   - encoding: F : D^r → C (C = algebraic complex numbers) → G : (Fin (j+1) → Fin q) → ℂ with every value IsAlgebraic ℚ; reason: the paper's C is the algebraic numbers in ℂ
-- source:
--   Liu, Meng, From Block Orthogonality to Decidability in Complex-Weighted Counting CSP, arXiv:2608.14845 (PDF sha256 ad21e5d7…), p. F-38, Lemma F.9.1

import Mathlib
import Definitions.Def_ConsModCount_Polymorphism
import Definitions.Def_BlockOrthoCSP_Decide_Rows

namespace BlockOrthoCSP.Decide

/-- Lemma F.9.1, p. F-38, for `F : D^{j+1} → ℂ` with algebraic values, `r = j + 1 ≥ 2`. -/
theorem lemma_F_9_1 {q : ℕ} (hq : 1 ≤ q) (j : ℕ) (hj : 1 ≤ j)
    (G : (Fin (j + 1) → Fin q) → ℂ) (hG : ∀ a, IsAlgebraic ℚ (G a))
    (φ : Fin q → Fin q → Fin q → Fin q) (hφ : ConsModCount.IsMaltsev φ)
    (hpres : ConsModCount.Preserves (ConsModCount.ternary φ) (Omega G)) :
    IsTypePartition G := by sorry

end BlockOrthoCSP.Decide
