-- Prove2me | Theorems.Thm_AlonMilman_Diameter_rayleigh_eq_2_1
-- name    : AlonMilman.Diameter.rayleigh_eq_2_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T17:26:20.345852+00:00
-- url     : https://prove2.me/theorems/9e778c92-e74f-49fb-b802-3e7423c24b7e
-- title:
--   Eq. (2.1) — Rayleigh's principle: $(Qf, f) \ge \lambda_1 \|f\|^2$ for $f \perp \mathbf 1$
-- statement:
--   Let $G = (V, E)$ be a connected finite simple graph on $n \ge 2$ vertices, with Laplacian $Q$ and algebraic connectivity $\lambda_1 = \lambda_1(G)$. Let $L^2(V)$ be the space of real functions on $V$ with scalar product $(f, g) = \sum_{v} f(v) g(v)$ and norm $\|f\| = \sqrt{(f,f)}$. If $f \in L^2(V)$ is orthogonal to the constants, i.e. $\sum_{v \in V} f(v) = 0$, then
--   $$
--   (Qf, f) \ge \lambda_1 \|f\|^2 .
--   $$
--
--   This is the variational side of $\lambda_1$: it converts the spectral definition into a lower bound for the quadratic form $(Qf, f) = \sum_{\{u,v\} \in E} (f(u) - f(v))^2$, and it is the only place where the eigenvalue enters the proof of Lemma 2.1.
--
--   **Formalization Note** $(f, g)$ is `dotProduct` (`⬝ᵥ`) and $Qf$ is `G.lapMatrix ℝ *ᵥ f`. $\lambda_1$ is defined spectrally (the mission's `lambda1`), so the statement is not definitional.
-- source:
--   Alon, Milman, λ1, Isoperimetric Inequalities for Graphs, and Superconcentrators, J. Combin. Theory Ser. B 38 (1985), p. 76, Section 2, Eq. (2.1)

import Mathlib
import Definitions.Def_AlonMilman_Diameter_lambda1
open Matrix

namespace AlonMilman.Diameter

theorem rayleigh_eq_2_1 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected) (hn : 2 ≤ Fintype.card V)
    (f : V → ℝ) (hf : ∑ v, f v = 0) :
    lambda1 G * (f ⬝ᵥ f) ≤ f ⬝ᵥ (G.lapMatrix ℝ *ᵥ f) := by sorry

end AlonMilman.Diameter
