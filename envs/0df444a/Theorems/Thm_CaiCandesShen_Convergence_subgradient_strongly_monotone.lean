-- Prove2me | Theorems.Thm_CaiCandesShen_Convergence_subgradient_strongly_monotone
-- name    : CaiCandesShen.Convergence.subgradient_strongly_monotone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:15:52.906786+00:00
-- url     : https://prove2.me/theorems/45e374a8-f4d9-449e-ba9d-6157c23e44a7
-- title:
--   Lemma 4.1 — $\langle Z-Z',X-X'\rangle\ge\|X-X'\|_F^2$ for subgradients of $f_\tau$
-- statement:
--   Let $\tau>0$ and $f_\tau(X)=\tau\|X\|_*+\tfrac12\|X\|_F^2$. If $Z\in\partial f_\tau(X)$ and $Z'\in\partial f_\tau(X')$, then
--   $$\langle Z-Z',X-X'\rangle\ge\|X-X'\|_F^2 .$$
--
--   This is the strong monotonicity of $\partial f_\tau$ (equivalently, strong convexity of $f_\tau$ with modulus $1$); the paper calls it key in showing that the SVT algorithm converges.
--
--   **Formalization Note** Subgradients are those of Eq. (2.4): $Z\in\partial f(X_0)$ iff $f(X)\ge f(X_0)+\langle Z,X-X_0\rangle$ for all $X$. The standing hypothesis $\tau>0$ of §3.1 is kept.
-- source:
--   Cai, Candès, Shen, A Singular Value Thresholding Algorithm for Matrix Completion, SIAM J. Optim. 20 (2010), p. 1968, Lemma 4.1, Eq. (4.1)

import Mathlib
import Definitions.Def_CaiCandesShen_Convergence_Basic

namespace CaiCandesShen.Convergence

/-- Lemma 4.1, p. 1968: if `Z ∈ ∂f_τ(X)` and `Z' ∈ ∂f_τ(X')`, then
`⟨Z - Z', X - X'⟩ ≥ ‖X - X'‖_F²`. -/
theorem subgradient_strongly_monotone {n₁ n₂ : ℕ} (τ : ℝ) (hτ : 0 < τ)
    (X X' Z Z' : Mat n₁ n₂) (hZ : IsSubgradient (fτ τ) X Z) (hZ' : IsSubgradient (fτ τ) X' Z') :
    frobNorm (X - X') ^ 2 ≤ frobInner (Z - Z') (X - X') := by sorry

end CaiCandesShen.Convergence
