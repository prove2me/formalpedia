-- Prove2me | Theorems.Thm_AffineStorage_Ruin_proposition_1
-- name    : AffineStorage.Ruin.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:36:25.940281+00:00
-- url     : https://prove2.me/theorems/4909e759-b297-4f5f-bd35-98ecf7caf0c0
-- title:
--   Proposition 1, p. 1287 (PDF 8) — φ′(ϑ) = F(ϑ)φ(ϑ) + G(ϑ)
-- statement:
--   Let $\varphi(\vartheta)=\int_0^\infty\vartheta e^{-\vartheta x}\varrho(x)\,dx$ be the transform of the expected discounted penalty at ruin before the exponential horizon. With $A=-(\alpha+\nu)/r$, let
--   $$F(\vartheta)=\frac pr-\frac{\lambda_-}r\frac{1-\delta(\vartheta)}\vartheta+\frac{\lambda_+}r\frac1{\mu-\vartheta}+\frac A\vartheta,\qquad G(\vartheta)=\frac{\lambda_-}r\frac{\delta(\beta)-\delta(\vartheta+\gamma)}{\vartheta+\gamma-\beta}-\frac pr\varrho(0)-\frac{\lambda_+}r\frac1{\mu-\vartheta}\varphi(\mu).$$
--   Then for every $\vartheta>0$ with $\vartheta\ne\mu$, $\varphi$ is differentiable at $\vartheta$ and
--   $$\varphi'(\vartheta)=F(\vartheta)\varphi(\vartheta)+G(\vartheta).\tag{6}$$
--
--   This first-order linear differential equation for $\varphi$ is obtained by transforming the integro-differential equation (4) term by term. Solving it by variation of constants gives Theorem 1.
--
--   **Formalization Note.** $r>0$ is assumed, as on the page ("Here we tacitly assumed r > 0"). At $\vartheta=\beta-\gamma$ the first term of $G$ takes its limit value.
-- source:
--   Boxma & Mandjes, Affine storage and insurance risk models, Math. Oper. Res. 46(4) (2021), p. 1287 (PDF 8), Proposition 1, eq. (6)

import Mathlib
import Definitions.Def_AffineStorage_Ruin_Model
open MeasureTheory ProbabilityTheory Filter Topology

namespace AffineStorage.Ruin

theorem proposition_1 (P : Params) (hS : P.Standing) {Ω : Type*} [MeasurableSpace Ω]
    (B : Basis Ω) (hB : B.IsValid P) (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑμ : ϑ ≠ P.μ) :
    HasDerivAt (phi B P)
      (F P ϑ * phi B P ϑ + G P (rho B P 0) (phi B P P.μ) ϑ) ϑ := by sorry

end AffineStorage.Ruin
