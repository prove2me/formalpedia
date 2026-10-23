-- Prove2me | Theorems.Thm_BoxTDIMinMax_Separable_lemma_3_2
-- name    : BoxTDIMinMax.Separable.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:06:30.061804+00:00
-- url     : https://prove2.me/theorems/7f079e4a-2643-43c7-b20e-a033853ab745
-- title:
--   Lemma 3.2, p. 13 — weak duality Φ(z) ≥ Φ(z∗) − y∗(Qz∗ − p) for Φ-compatible (z∗, y∗) with y∗ ≥ 0
-- statement:
--   Let $Q\in\mathbb Z^{I\times S}$, $p\in\mathbb Z^I$, $R=\{x:Qx\ge p\}$ and $\ddot R=R\cap\mathbb Z^S$. Let each $\varphi_s$ ($s\in S$) be discrete convex and $\Phi(z)=\sum_s\varphi_s(z(s))$. Suppose $z^*\in\ddot R$, $y^*\in\mathbb Z^I$ with $y^*\ge 0$, and $(z^*,y^*)$ is $\Phi$-compatible with respect to $Q$. Then
--   $$\Phi(z)\ \ge\ \Phi(z^*)-y^*(Qz^*-p)\qquad\text{for every } z\in\ddot R. \qquad (3.10)$$
--
--   This is the "min ≥ max" half of the min-max formula (3.14) and the "if" direction of the boundedness characterization in Theorem 3.3.
--
--   **Formalization Note** Written without subtraction as $\Phi(z^*)\le\Phi(z)+y^*(Qz^*-p)$ in $\mathbb Z\cup\{+\infty\}$ ($\Phi(z^*)$ is finite by compatibility). The section preamble's "integral polyhedron" and box-TDI-ness are not assumed: the statement holds for every integral system.
-- source:
--   Frank, Murota, A Discrete Convex Min-Max Formula for Box-TDI Polyhedra, arXiv:2007.03507v3, p. 13, Lemma 3.2, (3.10)

import Mathlib
import Definitions.Def_BoxTDIMinMax_Separable_Setting

namespace BoxTDIMinMax.Separable

open Matrix

/-- Lemma 3.2, p. 13, (3.10): weak duality. If `z* ∈ R̈`, `y* ≥ 0` is integral and `(z*, y*)` is
Φ-compatible, then `Φ(z) ≥ Φ(z*) - y*(Q z* - p)` for every `z ∈ R̈`, written without subtraction
as `Φ(z*) ≤ Φ(z) + y*(Q z* - p)`. -/
theorem lemma_3_2 {ι S : Type*} [Fintype ι] [Fintype S]
    (phi : S → ℤ → WithTop ℤ) (hphi : ∀ s, DiscConvex (phi s))
    (Q : Matrix ι S ℤ) (p : ι → ℤ) (zStar : S → ℤ) (hz : zStar ∈ intPts Q p)
    (yStar : ι → ℤ) (hy : 0 ≤ yStar) (hc : Compatible phi Q zStar yStar) :
    ∀ z ∈ intPts Q p,
      Phi phi zStar ≤ Phi phi z + ((yStar ⬝ᵥ (Q *ᵥ zStar - p) : ℤ) : WithTop ℤ) := by sorry

end BoxTDIMinMax.Separable
