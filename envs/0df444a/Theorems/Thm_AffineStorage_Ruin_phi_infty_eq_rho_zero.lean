-- Prove2me | Theorems.Thm_AffineStorage_Ruin_phi_infty_eq_rho_zero
-- name    : AffineStorage.Ruin.phi_infty_eq_rho_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:36:22.430056+00:00
-- url     : https://prove2.me/theorems/ca2fdedd-3482-478a-8dcf-adccc03df56f
-- title:
--   §2.3, p. 1285 (PDF 6) — φ(∞) = ϱ(0) ∈ (0, 1)
-- statement:
--   Let $\varrho(x)$ be the expected discounted penalty at ruin before the exponential horizon, started from $X_0=x$, and let $\varphi(\vartheta)=\int_0^\infty\vartheta e^{-\vartheta x}\varrho(x)\,dx$. Then
--   $$\lim_{\vartheta\to\infty}\varphi(\vartheta)=\varrho(0),\qquad 0<\varrho(0)<1 .$$
--   Here $\varrho(0)$ is the quantity for the process started at level $0$, with ruin time $\tau_0=\inf\{s>0:X_s\le0\}$.
--
--   The limit identifies the boundary value $\varrho(0)$, one of the two unknown constants in the closed form of Theorem 1, with the behaviour of $\varphi$ at infinity. That behaviour fixes the integration constant in the solution of the differential equation (6).
-- source:
--   Boxma & Mandjes, Affine storage and insurance risk models, Math. Oper. Res. 46(4) (2021), p. 1285 (PDF 6), §2.3

import Mathlib
import Definitions.Def_AffineStorage_Ruin_Model
open MeasureTheory ProbabilityTheory Filter Topology

namespace AffineStorage.Ruin

theorem phi_infty_eq_rho_zero (P : Params) (hS : P.Standing) {Ω : Type*} [MeasurableSpace Ω]
    (B : Basis Ω) (hB : B.IsValid P) :
    Tendsto (phi B P) atTop (𝓝 (rho B P 0)) ∧ 0 < rho B P 0 ∧ rho B P 0 < 1 := by sorry

end AffineStorage.Ruin
