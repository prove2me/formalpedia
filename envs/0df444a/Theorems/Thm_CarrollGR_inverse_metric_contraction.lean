-- Prove2me | Theorems.Thm_CarrollGR_inverse_metric_contraction
-- name    : CarrollGR.inverse_metric_contraction
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T23:49:57.868754+00:00
-- url     : https://prove2.me/theorems/1868b9db-4adc-4d7d-9838-5712f5ce344f
-- title:
--   $g^{\mu\nu}g_{\mu\nu}=4$
-- statement:
--   Let $g_{\mu\nu}$ be a real $4\times4$ matrix which is a metric of signature $(-+++)$, i.e. $P^{\mathsf T}gP=\eta$ for some invertible $P$, and let $g^{\mu\nu}$ be its inverse matrix. Then
--
--   $$g^{\mu\nu}g_{\mu\nu}=\delta^\mu_\mu=4 .$$
--
--   This is the basic trace identity used whenever one takes the trace of Einstein's equation (eq. (67)).
--
--   **Formalization Note** The statement is pointwise and purely algebraic; the signature hypothesis supplies symmetry and invertibility of $g$.
-- source:
--   S. M. Carroll, "A No-Nonsense Introduction to General Relativity" (lecture notes, 2001), uploaded PDF, p. 8, eq. (25)

import Mathlib
import Definitions.Def_CarrollGR_Defs

open scoped ContDiff

namespace CarrollGR

theorem inverse_metric_contraction (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : IsLorentzian M) :
    ∑ μ : Fin 4, ∑ ν : Fin 4, M⁻¹ μ ν * M μ ν = 4 := by sorry

end CarrollGR
