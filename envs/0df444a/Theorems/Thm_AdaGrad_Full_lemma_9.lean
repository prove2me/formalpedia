-- Prove2me | Theorems.Thm_AdaGrad_Full_lemma_9
-- name    : AdaGrad.Full.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:45:50.174209+00:00
-- url     : https://prove2.me/theorems/ee4db1d9-6fbc-4b5a-b5ba-2e6e9d0c0414
-- title:
--   Lemma 9 — $\langle g,(\delta I+A^{1/2})^{-1}g\rangle\le\langle g,((A+gg^\top)^\dagger)^{1/2}g\rangle$ when $\delta\ge\|g\|_2$
-- statement:
--   Let $g\in\mathbb R^d$, $\delta\ge\|g\|_2$, and let $A$ be a real symmetric positive semidefinite $d\times d$ matrix. Then
--   $$\big\langle g,(\delta I+A^{1/2})^{-1}g\big\rangle\le\Big\langle g,\big((A+gg^\top)^\dagger\big)^{1/2}g\Big\rangle.$$
--
--   With $A=G_{t-1}$ and $g=g_t$ it compares the dual norm $\|g_t\|_{\psi_{t-1}^*}^2$ of the primal-dual algorithm with $\langle g_t,S_t^\dagger g_t\rangle$.
--
--   **Formalization Note** The left side uses Mathlib's matrix inverse; $\delta I+A^{1/2}$ is invertible whenever $\delta>0$, and when $\delta=0$ the hypothesis forces $g=0$, so both sides vanish. The right side uses the functional-calculus pseudo-inverse and `CFC.sqrt`.
-- source:
--   Duchi, Hazan, Singer, Adaptive Subgradient Methods for Online Learning and Stochastic Optimization, JMLR 12 (2011), p. 2135, Lemma 9 (proof p. 2151)

import Mathlib
import Definitions.Def_AdaGrad_Full_Algorithm2
open scoped MatrixOrder InnerProductSpace

namespace AdaGrad.Full

/-- Lemma 9 (p. 2135): if `δ ≥ ‖g‖₂` and `A ⪰ 0` then
`⟨g, (δI + A^{1/2})^{−1} g⟩ ≤ ⟨g, ((A + g g⊤)†)^{1/2} g⟩`. -/
theorem lemma_9 {d : ℕ} (δ : ℝ) (g : EuclideanSpace ℝ (Fin d)) (hδ : ‖g‖ ≤ δ)
    (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosSemidef) :
    mInner (δ • (1 : Matrix (Fin d) (Fin d) ℝ) + CFC.sqrt A)⁻¹ g g
      ≤ mInner (CFC.sqrt (pinv (A + outer g))) g g := by sorry

end AdaGrad.Full
