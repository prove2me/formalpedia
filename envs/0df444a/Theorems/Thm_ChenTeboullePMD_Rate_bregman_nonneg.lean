-- Prove2me | Theorems.Thm_ChenTeboullePMD_Rate_bregman_nonneg
-- name    : ChenTeboullePMD.Rate.bregman_nonneg
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:39:10.180482+00:00
-- url     : https://prove2.me/theorems/f1907f0c-5ac7-4229-b8b7-1b41920aec88
-- title:
--   After Definition 2.1, p. 539 — nonnegativity and separation of the Bregman distance
-- statement:
--   Let $\psi$ be a Bregman function with open zone $S$. For $x\in\bar S$ and $y\in S$, its distance satisfies
--   $$
--   D_\psi(x,y)\ge0,\qquad D_\psi(x,y)=0\ \Longleftrightarrow\ x=y.
--   $$
--
--   This supplies the sign and equality case used throughout the PMD analysis.
--
--   **Formalization Note** The covector derivative defining $D_\psi$ is evaluated at $y\in S$, where $\psi$ is continuously differentiable. The ambient space is a real normed space; finite dimensionality is unnecessary for this remark.
-- source:
--   Chen & Teboulle, Convergence analysis of a proximal-like minimization algorithm using Bregman functions, SIAM J. Optim. 3 (1993), p. 539, paragraph after Definition 2.1

import Mathlib
import Definitions.Def_BeckTeboulleMD_EMDA_Setting
import Definitions.Def_ChenTeboullePMD_Rate_Setting

namespace ChenTeboullePMD.Rate

open BeckTeboulleMD.EMDA

/-- Remark after Definition 2.1, p. 539. -/
theorem bregman_nonneg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) (ψ : E → ℝ) (hψ : IsBregmanFunction S ψ) :
    ∀ x ∈ closure S, ∀ y ∈ S,
      0 ≤ bregman ψ x y ∧ (bregman ψ x y = 0 ↔ x = y) := by sorry

end ChenTeboullePMD.Rate
