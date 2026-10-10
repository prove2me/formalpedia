-- Prove2me | Theorems.Thm_FRBSplitting_Inertial_eq_43
-- name    : FRBSplitting.Inertial.eq_43
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:43:35.449604+00:00
-- url     : https://prove2.me/theorems/db239de6-ce29-45d4-b405-0fcd9e525534
-- title:
--   (43), proof of Theorem 4.3, p. 14 — ε := min{(2 − β(1+α))/2, (1 − α)/β} − λL′ > 0
-- statement:
--   Let $H$ be a real inner product space and $B:H\to H$ monotone. Let $L>0$, $\alpha\in[0,1)$, $\beta\in(0,1]$, $\lambda>0$, and suppose either
--
--   1. $B$ is $L$-Lipschitz and $\lambda<\min\Big\{\dfrac{2-\beta-\alpha\beta-2\alpha}{2L},\dfrac{1-\alpha-\alpha\beta}{\beta L}\Big\}$, or
--   2. $B$ is $\tfrac1L$-cocoercive, $\alpha<\dfrac{2-\beta}{2+\beta}$ and $\lambda<\min\Big\{\dfrac{2-\beta-\alpha\beta+2\alpha}{2L},\dfrac{1-\alpha+\alpha\beta}{\beta L}\Big\}$.
--
--   Then the operator $B':=B-\frac{\alpha}{\lambda}I$ has a Lipschitz constant $L'$ with
--
--   $$\varepsilon:=\min\Big\{\frac{2-\beta(1+\alpha)}{2},\frac{1-\alpha}{\beta}\Big\}-\lambda L'>0 .$$
--
--   This is the step where the step-size conditions (41)–(42) of Theorem 4.3 are converted, through Lemma 4.1, into a positive margin in the energy inequality of Lemma 4.2.
--
--   **Formalization Note.** The constant $L'$ is existential: it is a constant from Lemma 4.1 with $\rho=\alpha/\lambda$ ($L+\alpha/\lambda$ in case 1; $L-\alpha/\lambda$ or $\alpha/\lambda$ in case 2). $L>0$ is assumed because the bounds divide by $L$. No operator $A$ and no iteration enter.
-- source:
--   Malitsky & Tam, A Forward-Backward Splitting Method for Monotone Inclusions Without Cocoercivity, arXiv:1808.04162v4, p. 14, (43), proof of Theorem 4.3

import Mathlib
import Definitions.Def_ThreeOpSplitting_Accel_MonotoneOperators
import Definitions.Def_FRBSplitting_Inertial_Setting
open InnerProductSpace ThreeOpSplitting.Accel

namespace FRBSplitting.Inertial

theorem eq_43 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (B : H → H) (L α β lam : ℝ)
    (hBm : IsMonotoneFun B)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hlam : 0 < lam) (hL : 0 < L)
    (hcase : (IsLipschitzOp L B ∧
        lam < min ((2 - β - α * β - 2 * α) / (2 * L)) ((1 - α - α * β) / (β * L))) ∨
      (IsCocoercive L⁻¹ B ∧ α < (2 - β) / (2 + β) ∧
        lam < min ((2 - β - α * β + 2 * α) / (2 * L)) ((1 - α + α * β) / (β * L)))) :
    ∃ L' : ℝ, IsLipschitzOp L' (shiftOp B (α / lam)) ∧
      0 < min ((2 - β * (1 + α)) / 2) ((1 - α) / β) - lam * L' := by sorry

end FRBSplitting.Inertial
