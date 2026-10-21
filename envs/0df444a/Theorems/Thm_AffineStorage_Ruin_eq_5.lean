-- Prove2me | Theorems.Thm_AffineStorage_Ruin_eq_5
-- name    : AffineStorage.Ruin.eq_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:36:34.60683+00:00
-- url     : https://prove2.me/theorems/589ffb18-5047-43b9-88b3-40b5c2c5293e
-- title:
--   Eq. (5), p. 1286 (PDF 7) — transform of the upward-jump term
-- statement:
--   Let $\varrho$ be the expected discounted penalty at ruin and $\varphi$ its transform, and let $\mu>0$ be the rate of the exponential upward jumps. For every $\vartheta>0$ with $\vartheta\ne\mu$,
--   $$\lambda_+\int_0^\infty\Big(\int_0^\infty\mu e^{-\mu y}\varrho(x+y)\,dy\Big)\vartheta e^{-\vartheta x}\,dx=\lambda_+\frac{\mu}{\mu-\vartheta}\varphi(\vartheta)-\lambda_+\frac{\vartheta}{\mu-\vartheta}\varphi(\mu).$$
--
--   This is the transform of the third term on the right-hand side of (4). It brings the second unknown constant $\varphi(\mu)$ into the differential equation (6).
--
--   **Formalization Note.** The point $\vartheta=\mu$, a removable singularity on the page, is excluded.
-- source:
--   Boxma & Mandjes, Affine storage and insurance risk models, Math. Oper. Res. 46(4) (2021), p. 1286 (PDF 7), eq. (5)

import Mathlib
import Definitions.Def_AffineStorage_Ruin_Model
open MeasureTheory ProbabilityTheory Filter Topology

namespace AffineStorage.Ruin

theorem eq_5 (P : Params) (hS : P.Standing) {Ω : Type*} [MeasurableSpace Ω]
    (B : Basis Ω) (hB : B.IsValid P) (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑμ : ϑ ≠ P.μ) :
    P.lamPlus * (∫ x in Set.Ioi 0,
        (∫ y in Set.Ioi 0, P.μ * Real.exp (-(P.μ * y)) * rho B P (x + y))
          * (ϑ * Real.exp (-(ϑ * x))))
      = P.lamPlus * (P.μ / (P.μ - ϑ)) * phi B P ϑ
        - P.lamPlus * (ϑ / (P.μ - ϑ)) * phi B P P.μ := by sorry

end AffineStorage.Ruin
