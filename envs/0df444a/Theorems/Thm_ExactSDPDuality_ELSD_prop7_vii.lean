-- Prove2me | Theorems.Thm_ExactSDPDuality_ELSD_prop7_vii
-- name    : ExactSDPDuality.ELSD.prop7_vii
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T00:12:44.073333+00:00
-- url     : https://prove2.me/theorems/4478c9ec-846e-4a22-a8ba-f0d3a92de0e9
-- title:
--   Proposition 7(vii) — if U − WWᵀ ⪰ 0 then W = UH for some matrix H
-- statement:
--   Let $U, W$ be real $n\times n$ matrices with $U - WW^{\mathsf T}\succeq 0$ (positive semidefinite, in particular symmetric). Then there exists a real $n\times n$ matrix $H$, not necessarily symmetric, such that
--   $$W = UH .$$
--
--   Equivalently, the column space of $W$ is contained in that of $U$. In the recursive construction of the sets $\mathcal W_k$ this is what transfers the annihilation $Q(x)U_i = 0$ to $Q(x)W_i = 0$.
-- source:
--   Ramana, An exact duality theory for semidefinite programming and its complexity implications, Math. Program. 77 (1997), p. 139, Proposition 7(vii)

import Mathlib
import Definitions.Def_ExactSDPDuality_ELSD_Model

open Matrix

namespace ExactSDPDuality.ELSD

/-- Proposition 7(vii) (Ramana 1997, p. 139): if `U − WWᵀ ⪰ 0`, then `W = UH` for some
(not necessarily symmetric) real matrix `H`. -/
theorem prop7_vii {n : ℕ} (U W : Matrix (Fin n) (Fin n) ℝ)
    (h : (U - W * Wᵀ).PosSemidef) :
    ∃ H : Matrix (Fin n) (Fin n) ℝ, W = U * H := by sorry

end ExactSDPDuality.ELSD
