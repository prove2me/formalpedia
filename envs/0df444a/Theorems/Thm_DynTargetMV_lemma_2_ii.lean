-- Prove2me | Theorems.Thm_DynTargetMV_lemma_2_ii
-- name    : DynTargetMV.lemma_2_ii
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:39:56.729985+00:00
-- url     : https://prove2.me/theorems/0e9aac3b-cee2-425a-bb7f-00db75b1e58e
-- title:
--   Lemma 2 (ii) — (B.3) and (B.4) have the same optimizer, and $b^\top\hat y=d$
-- statement:
--   Let $\Sigma$ be a positive definite $m\times m$ matrix, $\varphi\in\mathbb R$, $b\in\mathbb R^m$ with $b\neq0$, $Q$ an $n\times m$ matrix, and $q\in\mathbb R^n$ with $q\le0$. Put $\rho:=b^\top\Sigma^{-1}b$. Fix $d\ge0$, and assume $\varphi\ge-d/\rho$ and that $\{y\in\mathbb R^m\mid b^\top y\ge d,\ Qy\ge q\}$ is nonempty. Then the problems
--   $$
--   \min_{y\in\mathbb R^m}\ \tfrac12y^\top\Sigma y+\varphi b^\top y\quad\text{subject to}\quad b^\top y\ge d,\ Qy\ge q \tag{B.3}
--   $$
--   and
--   $$
--   \min_{y\in\mathbb R^m}\ \tfrac12y^\top\Sigma y\quad\text{subject to}\quad b^\top y\ge d,\ Qy\ge q \tag{B.4}
--   $$
--   have the same unique optimal solution $\hat y$, and $b^\top\hat y=d$.
--
--   This identifies the optimizers of the first-order conditions (C.14), (C.22) with $v^*(t)$.
--
--   Differences from the source:
--   - reading: "Let ŷ be the optimal solution" → there is exactly one optimal solution ŷ, and the conclusion is stated for it; reason: the proof begins by showing that the optimal solution exists; it is unique by strict convexity
--   - encoding: Σ positive definite → Matrix.PosDef, which includes symmetry; reason: the lemma is applied to Σ = σσ⊤
-- source:
--   He & Jiang, Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth, Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, Lemma 2 (ii), p.22

import Definitions.Def_DynTargetMV_halfQuad
import Definitions.Def_DynTargetMV_IsOptimal

open Matrix

namespace DynTargetMV

/-- **Lemma 2 (ii).** Let `Σ` be positive definite, `b ≠ 0`, `q ≤ 0`, `ρ := b⊤Σ⁻¹b`. Fix `d ≥ 0`, assume
`φ ≥ −d/ρ` and `{y | b⊤y ≥ d, Qy ≥ q}` nonempty. Then (B.3), with objective `½y⊤Σy + φb⊤y`, and (B.4),
with objective `½y⊤Σy`, both subject to `b⊤y ≥ d`, `Qy ≥ q`, have the same unique optimal solution
`ŷ`, and `b⊤ŷ = d`. He & Jiang, *Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth*,
Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, Lemma 2 (ii), p.22. -/
theorem lemma_2_ii {m n : ℕ} (S : Matrix (Fin m) (Fin m) ℝ) (hS : S.PosDef) (φ : ℝ)
    (b : Fin m → ℝ) (hb : b ≠ 0) (Q : Matrix (Fin n) (Fin m) ℝ) (q : Fin n → ℝ) (hq : q ≤ 0)
    (d : ℝ) (hd : 0 ≤ d) (hφ : -d / (b ⬝ᵥ (S⁻¹ *ᵥ b)) ≤ φ)
    (hne : {y : Fin m → ℝ | d ≤ b ⬝ᵥ y ∧ q ≤ Q *ᵥ y}.Nonempty) :
    ∃ yh : Fin m → ℝ,
      (∀ y, IsOptimal (fun w => halfQuad S w + φ * (b ⬝ᵥ w)) {w | d ≤ b ⬝ᵥ w ∧ q ≤ Q *ᵥ w} y ↔
        y = yh) ∧
      (∀ y, IsOptimal (halfQuad S) {w | d ≤ b ⬝ᵥ w ∧ q ≤ Q *ᵥ w} y ↔ y = yh) ∧
      b ⬝ᵥ yh = d := by sorry

end DynTargetMV
