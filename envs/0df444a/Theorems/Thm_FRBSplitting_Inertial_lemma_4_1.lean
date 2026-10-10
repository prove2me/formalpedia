-- Prove2me | Theorems.Thm_FRBSplitting_Inertial_lemma_4_1
-- name    : FRBSplitting.Inertial.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:43:41.359983+00:00
-- url     : https://prove2.me/theorems/4cddd837-24a0-49f7-aebf-65b74493c94c
-- title:
--   Lemma 4.1, p. 11 — B − ρI is (L+ρ)-, (L−ρ)- or ρ-Lipschitz (36)
-- statement:
--   Let $H$ be a real inner product space, $B:H\to H$, $\rho\ge0$ and $B':=B-\rho I$. Then $B'$ is $L'$-Lipschitz, where
--
--   $$L'=\begin{cases}L+\rho & \text{if } B \text{ is } L\text{-Lipschitz},\\ L-\rho & \text{if } B \text{ is } \tfrac1L\text{-cocoercive and } \rho\le \tfrac L2,\\ \rho & \text{if } B \text{ is } \tfrac1L\text{-cocoercive and } \rho> \tfrac L2.\end{cases}$$
--
--   Here $B$ is $\tfrac1L$-cocoercive if $\tfrac1L\|B(x)-B(y)\|^2\le\langle B(x)-B(y),x-y\rangle$ for all $x,y$. The lemma supplies the Lipschitz constant of the operator $B'=B-(\alpha/\lambda)I$ that appears in the reformulation (35) of the relaxed inertial scheme.
--
--   **Formalization Note.** The three cases are three separate implications. The cocoercive cases assume $L>0$ (the page divides by $L$). The page's hypothesis "B monotone" is dropped: no case uses it, so the statement is stronger than printed.
-- source:
--   Malitsky & Tam, A Forward-Backward Splitting Method for Monotone Inclusions Without Cocoercivity, arXiv:1808.04162v4, p. 11, Lemma 4.1, (36)

import Mathlib
import Definitions.Def_ThreeOpSplitting_Accel_MonotoneOperators
import Definitions.Def_FRBSplitting_Inertial_Setting
open InnerProductSpace ThreeOpSplitting.Accel

namespace FRBSplitting.Inertial

theorem lemma_4_1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (B : H → H) (ρ L : ℝ) (hρ : 0 ≤ ρ) :
    (IsLipschitzOp L B → IsLipschitzOp (L + ρ) (shiftOp B ρ)) ∧
    (0 < L → IsCocoercive L⁻¹ B → ρ ≤ L / 2 → IsLipschitzOp (L - ρ) (shiftOp B ρ)) ∧
    (0 < L → IsCocoercive L⁻¹ B → L / 2 < ρ → IsLipschitzOp ρ (shiftOp B ρ)) := by sorry

end FRBSplitting.Inertial
