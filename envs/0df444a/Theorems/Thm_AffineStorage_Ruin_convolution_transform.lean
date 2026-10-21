-- Prove2me | Theorems.Thm_AffineStorage_Ruin_convolution_transform
-- name    : AffineStorage.Ruin.convolution_transform
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:36:22.520275+00:00
-- url     : https://prove2.me/theorems/9651a277-d14d-4438-aefe-2080d1c2c905
-- title:
--   §2.3, p. 1286 (PDF 7) — transform of the convolution term: λ−δ(ϑ)φ(ϑ)
-- statement:
--   Let $\varrho$ be the expected discounted penalty at ruin, $\varphi$ its transform, $d$ the claim density and $\delta(\vartheta)=\int_0^\infty e^{-\vartheta y}d(y)\,dy$. For every $\vartheta>0$,
--   $$\lambda_-\int_0^\infty\Big(\int_0^x d(y)\varrho(x-y)\,dy\Big)\vartheta e^{-\vartheta x}\,dx=\lambda_-\int_0^\infty e^{-\vartheta y}\Big(\int_y^\infty\varrho(x-y)\,\vartheta e^{-\vartheta(x-y)}\,dx\Big)d(y)\,dy=\lambda_-\delta(\vartheta)\varphi(\vartheta).$$
--
--   This is the transform of the first term on the right-hand side of (4), the claims that do not cause ruin. It is one of the inputs to Proposition 1.
-- source:
--   Boxma & Mandjes, Affine storage and insurance risk models, Math. Oper. Res. 46(4) (2021), p. 1286 (PDF 7), §2.3

import Mathlib
import Definitions.Def_AffineStorage_Ruin_Model
open MeasureTheory ProbabilityTheory Filter Topology

namespace AffineStorage.Ruin

theorem convolution_transform (P : Params) (hS : P.Standing) {Ω : Type*} [MeasurableSpace Ω]
    (B : Basis Ω) (hB : B.IsValid P) (ϑ : ℝ) (hϑ : 0 < ϑ) :
    P.lamMinus * (∫ x in Set.Ioi 0,
        (∫ y in Set.Ioc 0 x, P.d y * rho B P (x - y)) * (ϑ * Real.exp (-(ϑ * x))))
      = P.lamMinus * (∫ y in Set.Ioi 0, Real.exp (-(ϑ * y)) *
          (∫ x in Set.Ioi y, rho B P (x - y) * (ϑ * Real.exp (-(ϑ * (x - y))))) * P.d y) ∧
    P.lamMinus * (∫ y in Set.Ioi 0, Real.exp (-(ϑ * y)) *
          (∫ x in Set.Ioi y, rho B P (x - y) * (ϑ * Real.exp (-(ϑ * (x - y))))) * P.d y)
      = P.lamMinus * P.lst ϑ * phi B P ϑ := by sorry

end AffineStorage.Ruin
