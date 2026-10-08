-- Prove2me | Theorems.Thm_ConvexOptAlg_NesterovStrong_eq_3_21_form
-- name    : ConvexOptAlg.NesterovStrong.eq_3_21_form
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T18:00:44.927675+00:00
-- url     : https://prove2.me/theorems/4c8c6511-e2aa-469f-9995-c5fecd2c607c
-- title:
--   Proof of Theorem 3.18, p. 292 — Φ_s(x) = Φ*_s + (α/2)‖x − v_s‖² with v_s given by (3.21)
-- statement:
--   Let $\alpha>0$, $\beta\in\mathbb R$, $\kappa=\beta/\alpha$, let $f:\mathbb R^n\to\mathbb R$ and $g:\mathbb R^n\to\mathbb R^n$ be arbitrary (with $g$ in the role of $\nabla f$), and let $(x_s)_{s\ge1}$ be any sequence of points. Let $\Phi_s$ be defined by (3.17), let $v_1=x_1$ and
--   $$v_{s+1}=\Big(1-\frac1{\sqrt\kappa}\Big)v_s+\frac1{\sqrt\kappa}x_s-\frac1{\alpha\sqrt\kappa}\nabla f(x_s),\tag{3.21}$$
--   and let $\Phi^*_s=\Phi_s(v_s)$. Then for every $s\ge1$ and every $x\in\mathbb R^n$,
--   $$\Phi_s(x)=\Phi^*_s+\frac\alpha2\|x-v_s\|^2 .$$
--
--   In particular $\Phi_s$ is minimized at $v_s$ and $\Phi^*_s=\min_{x\in\mathbb R^n}\Phi_s(x)$, which is the book's definition of $\Phi^*_s$. This is the description of $\Phi_s$ through its centre on which the proof of (3.20) rests.
--
--   **Formalization Note** The identity is purely algebraic: it is stated for any sequence of points and any map $g$, without convexity or smoothness, which contains the case of a run. The book derives it from $\nabla^2\Phi_s=\alpha I_n$; no Hessian is stated here.
-- source:
--   Bubeck, arXiv:1405.4980v2, proof of Theorem 3.18, p. 292 (form of Φ_s and Eq. (3.21))

import Mathlib
import Definitions.Def_OnlineConvexOpt_ConvexBasics_StronglyConvexOn
import Definitions.Def_ConvexOptAlg_NesterovStrong_Defs

open scoped InnerProductSpace

namespace ConvexOptAlg.NesterovStrong

/-- Bubeck, proof of Theorem 3.18, p. 292 (the form of `Φ_s`, with `v_s` defined by (3.21)):
for any `α > 0`, any `f`, gradient map `g`, `β`, and any sequence of points `x_s`, the functions
`Φ_s` of (3.17) satisfy `Φ_s(z) = Φ∗_s + (α/2)‖z − v_s‖²` for every `s ≥ 1` and every `z`,
where `v₁ = x₁`, `v_{s+1} = (1 − 1/√κ) v_s + (1/√κ) x_s − (1/(α√κ)) ∇f(x_s)` and
`Φ∗_s = Φ_s(v_s)`. In particular `v_s` minimizes `Φ_s` and `Φ∗_s = min Φ_s`. -/
theorem eq_3_21_form {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (α β : ℝ)
    (hα : 0 < α) (x : ℕ → EuclideanSpace ℝ (Fin n))
    (s : ℕ) (hs : 1 ≤ s) (z : EuclideanSpace ℝ (Fin n)) :
    Phi f g α β x s z = PhiStar f g α β x s + α / 2 * ‖z - v g α β x s‖ ^ 2 := by sorry

end ConvexOptAlg.NesterovStrong
