-- Prove2me | Theorems.Thm_CatSymplectic_Hemistrict_exact_forms
-- name    : CatSymplectic.Hemistrict.exact_forms
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:39:45.810138+00:00
-- url     : https://prove2.me/theorems/72fe4e3d-fdc7-43bc-892d-f8ea293dbf8e
-- title:
--   p. 16 — exact one-forms are Hamiltonian
-- statement:
--   For every smooth real function \(f\) on a 2-plectic space, its exact form is Hamiltonian and
--
--   $$
--   v_{df}=0.
--   $$
--
--   This gives the differential from smooth functions to Hamiltonian one-forms in the two-term complex.
--
--   **Formalization Note** The space is a finite-dimensional real normed space. The differential \(df\) is ContWeatherall.grad, and the three-form \(\omega\) is named Ω in Lean.
-- source:
--   Baez, Hoffnung, Rogers, Categorified Symplectic Geometry and the Classical String, arXiv:0808.0246v1, p. 16, paragraph after the two-term complex

import Mathlib
import Definitions.Def_CatSymplectic_Hemistrict_Basic

namespace CatSymplectic.Hemistrict

theorem exact_forms {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (Ω : Form E 3) (hΩ : IsNPlectic 2 Ω)
    (f : E → ℝ) (hf : ContDiff ℝ smooth f) :
    ContWeatherall.grad f ∈ hamSubmodule Ω ∧
      hamVF Ω (ContWeatherall.grad f) = 0 := by sorry

end CatSymplectic.Hemistrict
