-- Prove2me | Theorems.Thm_CannonFloydParry_exists_isRationalSubdivision_refines_of_isIntegralSubdivision
-- name    : CannonFloydParry.exists_isRationalSubdivision_refines_of_isIntegralSubdivision
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-26T20:04:56.868857+00:00
-- url     : https://prove2.me/theorems/302ee7ae-cb6d-4761-ba8f-afa3079c5d0b
-- title:
--   p. 249 (after Rourke–Sanderson) — two integral subdivisions have a common rational refinement
-- statement:
--   For any two integral subdivisions $K_1$, $K_2$ of $\Delta_n$ there is a rational subdivision $K$ of $\Delta_n$ refining both.
--
--   **Source.** The notes obtain this from two results of Rourke and Sanderson (*Introduction to Piecewise-Linear Topology*, Exercise 5 p. 15 and Proposition 2.9): the intersection of the two subdivisions is a cell complex with rational vertices, which can be subdivided into a simplicial complex without new vertices. This statement is the conclusion drawn; it does not assert the intermediate cell complex or that no vertices are added.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathématique (2) 42 (1996) 215–256, https://doi.org/10.5169/seals-87877, section 7, p. 249, PIP homeomorphisms; citing Rourke, C. P., Sanderson, B. J., Introduction to Piecewise-Linear Topology, Ergebnisse der Mathematik und ihrer Grenzgebiete 69, Springer, 1972, https://doi.org/10.1007/978-3-642-81735-9, Exercise 5 p. 15 and Proposition 2.9

import Mathlib
import Definitions.Def_CannonFloydParry_PIP

namespace CannonFloydParry

theorem exists_isRationalSubdivision_refines_of_isIntegralSubdivision {n : ℕ}
    {K₁ K₂ : Geometry.SimplicialComplex ℝ (Fin (n + 1) → ℝ)}
    (h₁ : IsIntegralSubdivision n K₁) (h₂ : IsIntegralSubdivision n K₂) :
    ∃ K : Geometry.SimplicialComplex ℝ (Fin (n + 1) → ℝ),
      IsRationalSubdivision n K ∧ Refines K K₁ ∧ Refines K K₂ := by
  sorry

end CannonFloydParry
