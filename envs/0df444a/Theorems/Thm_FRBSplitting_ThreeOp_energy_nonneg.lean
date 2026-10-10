-- Prove2me | Theorems.Thm_FRBSplitting_ThreeOp_energy_nonneg
-- name    : FRBSplitting.ThreeOp.energy_nonneg
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:44:50.914722+00:00
-- url     : https://prove2.me/theorems/7b40325b-5cb3-4272-bff4-9170a3a5c6fe
-- title:
--   Proof of Theorem 5.2, p. 16 — the energy of Lemma 5.1 is bounded below by zero
-- statement:
--   Let $H$ be a real inner product space and $B:H\to H$ be $L_1$-Lipschitz with $L_1\ge0$. Let $L_2>0$ and
--
--   $$0<\lambda<\frac{2}{4L_1+L_2}.$$
--
--   Then for every sequence $(x_k)_{k\ge-1}$ in $H$, every point $x\in H$ and every $k\in\mathbb N$,
--
--   $$\|x_{k+1}-x\|^2+2\lambda\langle B(x_{k+1})-B(x_k),\,x-x_{k+1}\rangle+\lambda L_1\|x_{k+1}-x_k\|^2\ \ge\ 0.$$
--
--   The left-hand side is the energy that Lemma 5.1 shows to be nonincreasing along the three-operator scheme (47). Its nonnegativity is the remaining ingredient, beyond Lemma 5.1, of the proof of Theorem 5.2: together they make the energy convergent and the step lengths square-summable.
--
--   **Formalization Note.** Indices are shifted by one (Lean's `x j` is $x_{j-1}$). The statement holds for an arbitrary sequence and an arbitrary point $x$; the paper applies it to the iterates of (47) and a zero of $A+B+C$, so this is slightly more general than the claim in the proof. Monotonicity of $B$ is not needed. The hypothesis $L_2>0$ is the standing assumption of §5 that makes $C$ $\tfrac1{L_2}$-cocoercive; here it only enters through the step bound.
-- source:
--   Malitsky & Tam, A Forward-Backward Splitting Method for Monotone Inclusions Without Cocoercivity, arXiv:1808.04162v4, p. 16, proof of Theorem 5.2

import Mathlib
import Definitions.Def_ThreeOpSplitting_Accel_MonotoneOperators
import Definitions.Def_FRBSplitting_ThreeOp_Setting
open InnerProductSpace ThreeOpSplitting.Accel

namespace FRBSplitting.ThreeOp

theorem energy_nonneg {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (B : H → H) (L₁ L₂ lam : ℝ)
    (hL₁ : 0 ≤ L₁) (hBL : IsLipschitzOp L₁ B)
    (hL₂ : 0 < L₂)
    (hlam0 : 0 < lam) (hlam1 : lam < 2 / (4 * L₁ + L₂))
    (x : ℕ → H) (xs : H) :
    ∀ k : ℕ, 0 ≤ ‖x (k + 2) - xs‖ ^ 2 + 2 * lam * ⟪B (x (k + 2)) - B (x (k + 1)), xs - x (k + 2)⟫_ℝ
        + lam * L₁ * ‖x (k + 2) - x (k + 1)‖ ^ 2 := by sorry

end FRBSplitting.ThreeOp
