-- Prove2me | Theorems.Thm_CarrollGR_schwarzschild_unique_vacuum_solution
-- name    : CarrollGR.schwarzschild_unique_vacuum_solution
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-26T00:23:57.017511+00:00
-- url     : https://prove2.me/theorems/551a0728-602b-4eeb-8710-75482a589108
-- title:
--   Schwarzschild is the unique spherically symmetric vacuum solution
-- statement:
--   Let $G>0$, let $I=(t_1,t_2)$ and $J=(r_1,r_2)$ be open intervals with $r_1\ge0$, and let $A,B$ be smooth, strictly positive functions of $(r,t)\in J\times I$. Consider the general spherically symmetric metric (Carroll eq. (71))
--
--   $$ds^2=-A(r,t)\,dt^2+B(r,t)\,dr^2+r^2(d\theta^2+\sin^2\theta\,d\phi^2).$$
--
--   Then the following are equivalent:
--
--   1. the metric solves Einstein's equation in vacuum, $R_{\mu\nu}=0$, at every point with $r\in J$, $t\in I$, $0<\theta<\pi$;
--   2. there are a constant $m$ and a positive function $f(t)$ with
--   $$A(r,t)=f(t)\left(1-\frac{2Gm}{r}\right),\qquad B(r,t)=\left(1-\frac{2Gm}{r}\right)^{-1}\qquad(r\in J,\ t\in I),$$
--   i.e. the metric is the Schwarzschild metric (72) up to a reparametrization of $t$.
--
--   This is Carroll's statement "there is a unique solution: (72)" together with Birkhoff's theorem: the vacuum gravitational field around any spherically symmetric body is the Schwarzschild field.
--
--   **Formalization Note** "Unique" is necessarily up to rescaling $t$, hence the factor $f(t)$. The constant $m$ is not required to be positive; the positivity of $B$ forces $1-2Gm/r>0$ on $J$.
-- source:
--   S. M. Carroll, "A No-Nonsense Introduction to General Relativity" (lecture notes, 2001), uploaded PDF, p. 17, eqs. (69), (71), (72) and the following paragraph (Birkhoff's theorem)

import Mathlib
import Definitions.Def_CarrollGR_Defs

open scoped ContDiff

namespace CarrollGR

theorem schwarzschild_unique_vacuum_solution (GN : ℝ) (hGN : 0 < GN) (A B : ℝ → ℝ → ℝ)
    (r₁ r₂ t₁ t₂ : ℝ) (hr₁ : 0 ≤ r₁)
    (hA : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => A p.1 p.2) (Set.Ioo r₁ r₂ ×ˢ Set.Ioo t₁ t₂))
    (hB : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => B p.1 p.2) (Set.Ioo r₁ r₂ ×ˢ Set.Ioo t₁ t₂))
    (hApos : ∀ r ∈ Set.Ioo r₁ r₂, ∀ t ∈ Set.Ioo t₁ t₂, 0 < A r t)
    (hBpos : ∀ r ∈ Set.Ioo r₁ r₂, ∀ t ∈ Set.Ioo t₁ t₂, 0 < B r t) :
    (∀ x : Coord, x 1 ∈ Set.Ioo r₁ r₂ → x 0 ∈ Set.Ioo t₁ t₂ → x 2 ∈ Set.Ioo 0 Real.pi →
        ∀ μ ν : Fin 4, ricci (sphericalMetric A B) μ ν x = 0) ↔
      ∃ m : ℝ, ∃ f : ℝ → ℝ, ∀ r ∈ Set.Ioo r₁ r₂, ∀ t ∈ Set.Ioo t₁ t₂,
        0 < f t ∧ A r t = f t * (1 - 2 * GN * m / r) ∧ B r t = (1 - 2 * GN * m / r)⁻¹ := by sorry

end CarrollGR
