-- Prove2me | Theorems.Thm_AffineStorage_Ruin_drift_transforms
-- name    : AffineStorage.Ruin.drift_transforms
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:36:31.526323+00:00
-- url     : https://prove2.me/theorems/b2c5ddc5-798a-409a-a8b5-60c429b2e717
-- title:
--   §2.3, p. 1286 (PDF 7) — transforms of the drift terms of (4) and the identity for φ′
-- statement:
--   Let $\varrho$ be the expected discounted penalty at ruin and $\varphi(\vartheta)=\int_0^\infty\vartheta e^{-\vartheta x}\varrho(x)\,dx$. For every $\vartheta>0$:
--
--   1. $$-\int_0^\infty\varrho'(x)\,p\,\vartheta e^{-\vartheta x}\,dx=p\vartheta\big(\varrho(0)-\varphi(\vartheta)\big);$$
--   2. $$-\int_0^\infty\varrho'(x)\,rx\,\vartheta e^{-\vartheta x}\,dx=r\vartheta\int_0^\infty\varrho(x)\big(e^{-\vartheta x}-x\vartheta e^{-\vartheta x}\big)\,dx=r\vartheta\,\varphi'(\vartheta);$$
--   3. $\varphi$ is differentiable at $\vartheta$, with
--   $$\varphi'(\vartheta)=\frac{\varphi(\vartheta)}\vartheta-\int_0^\infty x\vartheta e^{-\vartheta x}\varrho(x)\,dx .$$
--
--   These are the transforms of the two drift terms on the left-hand side of (4), obtained by integration by parts. They are two of the inputs from which the differential equation (6) of Proposition 1 is assembled.
-- source:
--   Boxma & Mandjes, Affine storage and insurance risk models, Math. Oper. Res. 46(4) (2021), p. 1286 (PDF 7), §2.3

import Mathlib
import Definitions.Def_AffineStorage_Ruin_Model
open MeasureTheory ProbabilityTheory Filter Topology

namespace AffineStorage.Ruin

theorem drift_transforms (P : Params) (hS : P.Standing) {Ω : Type*} [MeasurableSpace Ω]
    (B : Basis Ω) (hB : B.IsValid P) (ϑ : ℝ) (hϑ : 0 < ϑ) :
    -(∫ x in Set.Ioi 0, deriv (rho B P) x * P.p * (ϑ * Real.exp (-(ϑ * x))))
        = P.p * ϑ * (rho B P 0 - phi B P ϑ) ∧
    -(∫ x in Set.Ioi 0, deriv (rho B P) x * (P.r * x) * (ϑ * Real.exp (-(ϑ * x))))
        = P.r * ϑ * ∫ x in Set.Ioi 0,
            rho B P x * (Real.exp (-(ϑ * x)) - x * (ϑ * Real.exp (-(ϑ * x)))) ∧
    P.r * ϑ * (∫ x in Set.Ioi 0,
            rho B P x * (Real.exp (-(ϑ * x)) - x * (ϑ * Real.exp (-(ϑ * x)))))
        = P.r * ϑ * deriv (phi B P) ϑ ∧
    HasDerivAt (phi B P)
      (phi B P ϑ / ϑ - ∫ x in Set.Ioi 0, x * (ϑ * Real.exp (-(ϑ * x))) * rho B P x) ϑ := by sorry

end AffineStorage.Ruin
