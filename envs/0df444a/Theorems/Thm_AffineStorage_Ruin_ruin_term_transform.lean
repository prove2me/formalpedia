-- Prove2me | Theorems.Thm_AffineStorage_Ruin_ruin_term_transform
-- name    : AffineStorage.Ruin.ruin_term_transform
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:36:23.562038+00:00
-- url     : https://prove2.me/theorems/dccffbac-4a16-4840-a3d1-61bf4bd64fe9
-- title:
--   §2.3, p. 1286 (PDF 7) — transform of the ruin term; ϑ = β − γ is a removable singularity
-- statement:
--   Let $d$ be the claim density with Laplace–Stieltjes transform $\delta$, and let $\beta,\gamma\ge0$. For $\vartheta>0$ write
--   $$L(\vartheta)=\lambda_-\int_0^\infty\Big(\int_x^\infty d(y)e^{-\beta(y-x)}e^{-\gamma x}\,dy\Big)\vartheta e^{-\vartheta x}\,dx .$$
--
--   1. If $\vartheta+\gamma\ne\beta$, then
--   $$L(\vartheta)=\lambda_-\vartheta\int_0^\infty\frac{e^{-\beta y}-e^{-(\vartheta+\gamma)y}}{\vartheta+\gamma-\beta}\,d(y)\,dy=\lambda_-\vartheta\,\frac{\delta(\beta)-\delta(\vartheta+\gamma)}{\vartheta+\gamma-\beta}.$$
--   2. For every $\vartheta>0$, $L(\vartheta)=r\vartheta\,G_3(\vartheta)$, where $G_3(\vartheta)=\frac{\lambda_-}r\frac{\delta(\beta)-\delta(\vartheta+\gamma)}{\vartheta+\gamma-\beta}$ and, at $\vartheta=\beta-\gamma$, $G_3$ takes its limit value $\frac{\lambda_-}r\int_0^\infty ye^{-\beta y}d(y)\,dy$. This is the page's remark that $\vartheta=\beta-\gamma$ is a removable singularity.
--
--   This is the transform of the second term on the right-hand side of (4), the claims that cause ruin. It produces the function $G_3$ in the inhomogeneous term of (6).
-- source:
--   Boxma & Mandjes, Affine storage and insurance risk models, Math. Oper. Res. 46(4) (2021), p. 1286 (PDF 7), §2.3

import Mathlib
import Definitions.Def_AffineStorage_Ruin_Model
open MeasureTheory ProbabilityTheory Filter Topology

namespace AffineStorage.Ruin

theorem ruin_term_transform (P : Params) (hS : P.Standing) (ϑ : ℝ) (hϑ : 0 < ϑ) :
    (ϑ + P.γ ≠ P.β →
      P.lamMinus * (∫ x in Set.Ioi 0,
          (∫ y in Set.Ioi x, P.d y * Real.exp (-(P.β * (y - x))) * Real.exp (-(P.γ * x)))
            * (ϑ * Real.exp (-(ϑ * x))))
        = P.lamMinus * ϑ * (∫ y in Set.Ioi 0,
            (Real.exp (-(P.β * y)) - Real.exp (-((ϑ + P.γ) * y))) / (ϑ + P.γ - P.β) * P.d y) ∧
      P.lamMinus * ϑ * (∫ y in Set.Ioi 0,
            (Real.exp (-(P.β * y)) - Real.exp (-((ϑ + P.γ) * y))) / (ϑ + P.γ - P.β) * P.d y)
        = P.lamMinus * ϑ * ((P.lst P.β - P.lst (ϑ + P.γ)) / (ϑ + P.γ - P.β))) ∧
    P.lamMinus * (∫ x in Set.Ioi 0,
        (∫ y in Set.Ioi x, P.d y * Real.exp (-(P.β * (y - x))) * Real.exp (-(P.γ * x)))
          * (ϑ * Real.exp (-(ϑ * x))))
      = P.r * ϑ * G3 P ϑ := by sorry

end AffineStorage.Ruin
