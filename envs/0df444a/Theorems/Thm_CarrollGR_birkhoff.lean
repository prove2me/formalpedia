-- Prove2me | Theorems.Thm_CarrollGR_birkhoff
-- name    : CarrollGR.birkhoff
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-26T00:15:30.956132+00:00
-- url     : https://prove2.me/theorems/65f97e0f-2dd4-405f-9ec6-dbf93e8c8655
-- title:
--   Birkhoff's theorem (uniqueness of the spherically symmetric vacuum solution)
-- statement:
--   Let $G>0$, let $I=(t_1,t_2)$ and $J=(r_1,r_2)$ be open intervals with $r_1\ge0$, and let $A,B$ be smooth, strictly positive functions of $(r,t)\in J\times I$. Suppose the spherically symmetric metric
--
--   $$ds^2=-A(r,t)\,dt^2+B(r,t)\,dr^2+r^2(d\theta^2+\sin^2\theta\,d\phi^2)$$
--
--   satisfies the vacuum Einstein equation $R_{\mu\nu}=0$ at every point with $r\in J$, $t\in I$, $0<\theta<\pi$. Then there are a constant $m$ and a positive function $f$ of $t$ such that for all $r\in J$, $t\in I$
--
--   $$A(r,t)=f(t)\left(1-\frac{2Gm}{r}\right),\qquad B(r,t)=\left(1-\frac{2Gm}{r}\right)^{-1}.$$
--
--   After the time reparametrization $dt'=\sqrt{f(t)}\,dt$ this is exactly the Schwarzschild metric (72): the gravitational field outside any spherically symmetric distribution of matter is static and depends only on one constant.
--
--   **Formalization Note** Carroll's "unique" is necessarily up to the freedom of rescaling $t$, which is why the factor $f(t)$ appears. The constant $m$ is not required to be positive.
-- source:
--   S. M. Carroll, "A No-Nonsense Introduction to General Relativity" (lecture notes, 2001), uploaded PDF, p. 17, eqs. (71)–(72) and the paragraph following (72) (Birkhoff's theorem)

import Mathlib
import Definitions.Def_CarrollGR_Defs

open scoped ContDiff

namespace CarrollGR

theorem birkhoff (GN : ℝ) (hGN : 0 < GN) (A B : ℝ → ℝ → ℝ) (r₁ r₂ t₁ t₂ : ℝ) (hr₁ : 0 ≤ r₁)
    (hA : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => A p.1 p.2) (Set.Ioo r₁ r₂ ×ˢ Set.Ioo t₁ t₂))
    (hB : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => B p.1 p.2) (Set.Ioo r₁ r₂ ×ˢ Set.Ioo t₁ t₂))
    (hApos : ∀ r ∈ Set.Ioo r₁ r₂, ∀ t ∈ Set.Ioo t₁ t₂, 0 < A r t)
    (hBpos : ∀ r ∈ Set.Ioo r₁ r₂, ∀ t ∈ Set.Ioo t₁ t₂, 0 < B r t)
    (hvac : ∀ x : Coord, x 1 ∈ Set.Ioo r₁ r₂ → x 0 ∈ Set.Ioo t₁ t₂ → x 2 ∈ Set.Ioo 0 Real.pi →
      ∀ μ ν : Fin 4, ricci (sphericalMetric A B) μ ν x = 0) :
    ∃ m : ℝ, ∃ f : ℝ → ℝ, ∀ r ∈ Set.Ioo r₁ r₂, ∀ t ∈ Set.Ioo t₁ t₂,
      0 < f t ∧ A r t = f t * (1 - 2 * GN * m / r) ∧ B r t = (1 - 2 * GN * m / r)⁻¹ := by sorry

end CarrollGR
