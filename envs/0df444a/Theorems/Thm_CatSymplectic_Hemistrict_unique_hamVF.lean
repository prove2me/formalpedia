-- Prove2me | Theorems.Thm_CatSymplectic_Hemistrict_unique_hamVF
-- name    : CatSymplectic.Hemistrict.unique_hamVF
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:39:45.91571+00:00
-- url     : https://prove2.me/theorems/296c6cba-ab98-47d7-a763-1ffa7e9f5f14
-- title:
--   p. 11 — uniqueness of the Hamiltonian vector field
-- statement:
--   Let \(\omega\) be 2-plectic and \(F\) a one-form. If vector fields \(v,w\) both satisfy the Hamiltonian equation for \(F\), then
--
--   $$
--   v=w=v_F.
--   $$
--
--   Thus every Hamiltonian one-form has a unique associated vector field.
--
--   **Formalization Note** The manifold is restricted to a finite-dimensional real normed space, and the witnesses are smooth. The paper's \(\omega\) is named Ω in Lean.
-- source:
--   Baez, Hoffnung, Rogers, Categorified Symplectic Geometry and the Classical String, arXiv:0808.0246v1, p. 11, paragraph after Definition 3.1

import Mathlib
import Definitions.Def_CatSymplectic_Hemistrict_Basic

namespace CatSymplectic.Hemistrict

theorem unique_hamVF {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (Ω : Form E 3) (hΩ : IsNPlectic 2 Ω)
    (F : Form E 1) (v w : E → E)
    (hv : IsHamVF Ω F v) (hw : IsHamVF Ω F w) :
    v = w ∧ hamVF Ω F = v := by sorry

end CatSymplectic.Hemistrict
