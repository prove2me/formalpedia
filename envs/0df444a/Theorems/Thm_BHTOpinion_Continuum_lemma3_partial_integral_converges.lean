-- Prove2me | Theorems.Thm_BHTOpinion_Continuum_lemma3_partial_integral_converges
-- name    : BHTOpinion.Continuum.lemma3_partial_integral_converges
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:41:10.40672+00:00
-- url     : https://prove2.me/theorems/49badc0d-a1a2-4fb4-914b-2b67ef38b045
-- title:
--   Lemma 3 — for a nondecreasing solution of (3.2), ∫_0^c x_t(α) dα and the averages over [b, c] converge
-- statement:
--   Let $x$ be a solution of the integral equation (3.2) (for some initial condition) such that $x_t$ is nondecreasing on $I=[0,1]$ for every $t\ge0$. Then for every $c\in I$ the limit
--
--   $$\lim_{t\to\infty}\int_0^c x_t(\alpha)\,d\alpha$$
--
--   exists in $\mathbb R$. As a consequence, for every $b<c$ in $I$ the average value $\frac{1}{c-b}\int_b^c x_t(\alpha)\,d\alpha$ of $x_t$ on $[b,c]$ converges as $t\to\infty$.
--
--   This is the first step towards the convergence of opinions: it controls the mass of opinions to the left of any agent.
--
--   **Formalization Note** "Nondecreasing solution" is the paper's convention of p. 5222: $x_t\in X$ for all $t$. "The limit exists" is stated as convergence to a real number.
-- source:
--   Blondel, Hendrickx, Tsitsiklis, SIAM J. Control Optim. 48 (2010), Lemma 3, pp. 5225–5226

import Mathlib
import Definitions.Def_BHTOpinion_Continuum_Model

open MeasureTheory Filter Topology

namespace BHTOpinion.Continuum

theorem lemma3_partial_integral_converges (x0 : ℝ → ℝ) (x : ℝ → ℝ → ℝ)
    (hx : IsSolution x0 x) (hmono : ∀ t : ℝ, 0 ≤ t → InX (x t)) :
    (∀ c ∈ I, ∃ l : ℝ, Tendsto (fun t => ∫ α in (0 : ℝ)..c, x t α) atTop (𝓝 l)) ∧
      ∀ b ∈ I, ∀ c ∈ I, b < c →
        ∃ l : ℝ, Tendsto (fun t => (∫ α in b..c, x t α) / (c - b)) atTop (𝓝 l) := by sorry

end BHTOpinion.Continuum
