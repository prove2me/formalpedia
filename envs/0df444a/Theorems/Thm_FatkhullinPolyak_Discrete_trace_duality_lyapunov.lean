-- Prove2me | Theorems.Thm_FatkhullinPolyak_Discrete_trace_duality_lyapunov
-- name    : FatkhullinPolyak.Discrete.trace_duality_lyapunov
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:35:31.649286+00:00
-- url     : https://prove2.me/theorems/ed9ec995-4c49-4247-8f34-41cdb0c4e6a0
-- title:
--   Lemma A.1 — trace duality of dual Lyapunov equations, $\mathrm{Tr}(XV)=\mathrm{Tr}(YW)$
-- statement:
--   Let $A\in\mathbb R^{n\times n}$ be Hurwitz and let $W,V\in\mathbb R^{n\times n}$. Let $X$ and $Y$ solve the dual Lyapunov equations
--   $$A^\top X + XA + W = 0,\qquad AY + YA^\top + V = 0 .$$
--   Then
--   $$\mathrm{Tr}(XV)=\mathrm{Tr}(YW).$$
--
--   This identity lets the cost $f(K)=\mathrm{Tr}(X(K)\Sigma)$ be rewritten as $\mathrm{Tr}\big(Y(K)(Q+C^\top K^\top RKC)\big)$, which is how the lower bounds of Lemma 3.8 and Lemma C.2 are obtained.
-- source:
--   Fatkhullin, Polyak, Optimizing Static Linear Feedback: Gradient Method, arXiv:2004.09875v2, p. 15, Lemma A.1

import Mathlib
import Definitions.Def_FatkhullinPolyak_Discrete_Matrix

namespace FatkhullinPolyak.Discrete

/-- Lemma A.1 (p. 15): for Hurwitz `A`, solutions `X`, `Y` of the dual Lyapunov equations
`AᵀX + XA + W = 0` and `AY + YAᵀ + V = 0` satisfy `Tr(XV) = Tr(YW)`. -/
theorem trace_duality_lyapunov {n : ℕ} (A X Y W V : Matrix (Fin n) (Fin n) ℝ)
    (hA : IsHurwitz A)
    (hX : A.transpose * X + X * A + W = 0)
    (hY : A * Y + Y * A.transpose + V = 0) :
    Matrix.trace (X * V) = Matrix.trace (Y * W) := by sorry

end FatkhullinPolyak.Discrete
