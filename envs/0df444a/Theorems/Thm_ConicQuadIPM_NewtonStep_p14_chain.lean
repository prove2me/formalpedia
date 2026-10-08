-- Prove2me | Theorems.Thm_ConicQuadIPM_NewtonStep_p14_chain
-- name    : ConicQuadIPM.NewtonStep.p14_chain
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T03:09:43.999493+00:00
-- url     : https://prove2.me/theorems/0949f051-b912-4713-b363-3bb25d39ee33
-- title:
--   Proof of Lemma 4.1, p. 14 — (x⁽⁰⁾)ᵀd_s + (s⁽⁰⁾)ᵀd_x + τ⁽⁰⁾d_κ + κ⁽⁰⁾d_τ = (γ − 1)µ⁽⁰⁾(k + 1) (page prints k)
-- statement:
--   In the setting of the Newton system (22) — a product cone $K = K^1\times\cdots\times K^k$ with the usual dimension conventions, data $A$, $b$, $c$, any point $(x^{(0)},\tau^{(0)},y^{(0)},s^{(0)},\kappa^{(0)})$, $\gamma\in[0,1]$ and a solution $(d_x,d_\tau,d_y,d_s,d_\kappa)$ of (22) — with
--   $$
--   \mu^{(0)} = \frac{(x^{(0)})^Ts^{(0)} + \tau^{(0)}\kappa^{(0)}}{k+1},
--   $$
--   one has
--   $$
--   (x^{(0)})^Td_s + (s^{(0)})^Td_x + \tau^{(0)}d_\kappa + \kappa^{(0)}d_\tau = (\gamma-1)\,\mu^{(0)}\,(k+1).
--   $$
--   Equivalently, the left-hand side equals $(\gamma-1)\big((x^{(0)})^Ts^{(0)} + \tau^{(0)}\kappa^{(0)}\big)$.
--
--   This is the value of the linear term in (26). Combined with (26) it gives the orthogonality of the direction and the reduction of the complementarity gap in Lemma 4.1.
--
--   **Formalization Note** The page ends the chain with $(\gamma-1)\mu^{(0)}k$. That constant is a slip: $e^Te = k$, so the chain evaluates to $-(x^{(0)})^Ts^{(0)} + \gamma\mu^{(0)}k - \tau^{(0)}\kappa^{(0)} + \gamma\mu^{(0)} = (\gamma-1)\mu^{(0)}(k+1)$, and the printed value is false whenever $\gamma\ne1$ and $\mu^{(0)}\ne0$ (for $k=1$, one $\mathbb R_+$ block, $x^{(0)}=s^{(0)}=\tau^{(0)}=\kappa^{(0)}=1$, $\gamma=1/2$, the left side is $-1$ and the printed value is $-1/2$). The corrected constant $k+1$ is the one Lemma 4.1 needs. The hypothesis $\gamma\in[0,1]$ is the range of (21) and is not needed.
-- source:
--   Andersen, Roos & Terlaky, On implementing a primal-dual interior-point method for conic quadratic optimization, Math. Program. (2003); authors' preprint of 18 Dec 2000, p. 14, proof of Lemma 4.1, the display after 'Moreover,' (final constant corrected from k to k + 1)

import Mathlib
import Definitions.Def_ConicQuadIPM_NewtonStep_Setting

namespace ConicQuadIPM.NewtonStep

open Matrix

theorem p14_chain
    {m k : ℕ} (kind : Fin k → ConicQuadIPM.Complementarity.ConeKind) (n : Fin k → ℕ) (hwf : ConicQuadIPM.Complementarity.WellFormed kind n)
    (A : (i : Fin k) → Matrix (Fin m) (Fin (n i)) ℝ) (b : Fin m → ℝ)
    (c : (i : Fin k) → Fin (n i) → ℝ)
    (x0 : (i : Fin k) → Fin (n i) → ℝ) (τ0 : ℝ) (y0 : Fin m → ℝ)
    (s0 : (i : Fin k) → Fin (n i) → ℝ) (κ0 : ℝ) (γ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1)
    (dx : (i : Fin k) → Fin (n i) → ℝ) (dτ : ℝ) (dy : Fin m → ℝ)
    (ds : (i : Fin k) → Fin (n i) → ℝ) (dκ : ℝ)
    (h22 : NewtonSystem kind n A b c x0 τ0 y0 s0 κ0 γ dx dτ dy ds dκ) :
    (∑ i, x0 i ⬝ᵥ ds i) + (∑ i, s0 i ⬝ᵥ dx i) + τ0 * dκ + κ0 * dτ
      = (γ - 1) * mu0 x0 τ0 s0 κ0 * ((k : ℝ) + 1) := by sorry

end ConicQuadIPM.NewtonStep
