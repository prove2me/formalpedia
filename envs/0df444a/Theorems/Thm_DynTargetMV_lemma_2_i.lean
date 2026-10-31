-- Prove2me | Theorems.Thm_DynTargetMV_lemma_2_i
-- name    : DynTargetMV.lemma_2_i
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:39:52.019501+00:00
-- url     : https://prove2.me/theorems/7bda4e2d-593a-4156-9f8e-3b220f7c6f26
-- title:
--   Lemma 2 (i) — $b^\top\hat y\le\max\{-\varphi,0\}\rho$
-- statement:
--   Let $\Sigma$ be a positive definite $m\times m$ matrix, $\varphi\in\mathbb R$, $b\in\mathbb R^m$ with $b\neq0$, $Q$ an $n\times m$ matrix, and $q\in\mathbb R^n$ with $q\le0$. Put $\rho:=b^\top\Sigma^{-1}b$.
--   The problem
--   $$
--   \min_{y\in\mathbb R^m}\ \tfrac12y^\top\Sigma y+\varphi b^\top y\quad\text{subject to}\quad Qy\ge q \tag{B.2}
--   $$
--   has a unique optimal solution $\hat y$, and
--   $$
--   b^\top\hat y\le\max\{-\varphi,0\}\,\rho .
--   $$
--   The proof of Theorem 1 uses this bound to exclude times at which the target is slack.
--
--   Differences from the source:
--   - reading: "Let ŷ be the optimal solution" → there is exactly one optimal solution ŷ, and the conclusion is stated for it; reason: the proof begins by showing that the optimal solution exists; it is unique by strict convexity
--   - encoding: Σ positive definite → Matrix.PosDef, which includes symmetry; reason: the lemma is applied to Σ = σσ⊤
-- source:
--   He & Jiang, Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth, Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, Lemma 2 (i), p.22

import Definitions.Def_DynTargetMV_halfQuad
import Definitions.Def_DynTargetMV_IsOptimal

open Matrix

namespace DynTargetMV

/-- **Lemma 2 (i).** Let `Σ` be positive definite, `b ≠ 0`, `q ≤ 0`, `ρ := b⊤Σ⁻¹b`. Problem (B.2),
`min ½y⊤Σy + φb⊤y` subject to `Qy ≥ q`, has a unique optimal solution `ŷ`, and `b⊤ŷ ≤ max{−φ,0}ρ`.
He & Jiang, *Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth*,
Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, Lemma 2 (i), p.22.

**Formalization Note** "Let ŷ be the optimal solution" is stated as existence and uniqueness of `ŷ`
(proved at the start of the proof of Lemma 2). -/
theorem lemma_2_i {m n : ℕ} (S : Matrix (Fin m) (Fin m) ℝ) (hS : S.PosDef) (φ : ℝ)
    (b : Fin m → ℝ) (hb : b ≠ 0) (Q : Matrix (Fin n) (Fin m) ℝ) (q : Fin n → ℝ) (hq : q ≤ 0) :
    ∃ yh : Fin m → ℝ,
      (∀ y, IsOptimal (fun w => halfQuad S w + φ * (b ⬝ᵥ w)) {w | q ≤ Q *ᵥ w} y ↔ y = yh) ∧
      b ⬝ᵥ yh ≤ max (-φ) 0 * (b ⬝ᵥ (S⁻¹ *ᵥ b)) := by sorry

end DynTargetMV
