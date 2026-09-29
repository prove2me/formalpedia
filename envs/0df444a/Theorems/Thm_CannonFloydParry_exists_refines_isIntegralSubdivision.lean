-- Prove2me | Theorems.Thm_CannonFloydParry_exists_refines_isIntegralSubdivision
-- name    : CannonFloydParry.exists_refines_isIntegralSubdivision
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-26T20:05:41.882144+00:00
-- url     : https://prove2.me/theorems/29458e54-2c6d-4b18-a494-d25e107b0a66
-- title:
--   Theorem 7.1 — every rational subdivision of Δₙ has an integral refinement
-- statement:
--   Every rational subdivision $K$ of $\Delta_n$ has a refinement $K'$ that is an integral subdivision of $\Delta_n$.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathématique (2) 42 (1996) 215–256, https://doi.org/10.5169/seals-87877, section 7, p. 249, Theorem 7.1

import Mathlib
import Definitions.Def_CannonFloydParry_PIP

namespace CannonFloydParry

theorem exists_refines_isIntegralSubdivision {n : ℕ}
    {K : Geometry.SimplicialComplex ℝ (Fin (n + 1) → ℝ)} (hK : IsRationalSubdivision n K) :
    ∃ K' : Geometry.SimplicialComplex ℝ (Fin (n + 1) → ℝ),
      Refines K' K ∧ IsIntegralSubdivision n K' := by
  sorry

end CannonFloydParry
