-- Prove2me | Theorems.Thm_CatSymplectic_Hemistrict_proposition_3_6_1
-- name    : CatSymplectic.Hemistrict.proposition_3_6_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:39:52.475678+00:00
-- url     : https://prove2.me/theorems/eb4463f7-aa95-42ca-bb36-701a67e3714d
-- title:
--   Proposition 3.6(1), p. 12 — closure of the hemi-bracket
-- statement:
--   For Hamiltonian one-forms \(F,G\), the hemi-bracket is Hamiltonian and its vector field is their vector-field bracket:
--
--   $$
--   d\{F,G\}_h=-\iota_{[v_F,v_G]}\omega,\qquad
--   v_{\{F,G\}_h}=[v_F,v_G].
--   $$
--
--   This supplies closure and identifies the field of a nested bracket.
--
--   **Formalization Note** This is the \(n=2\) case on a finite-dimensional real normed space. The paper's \(\omega\) is Ω in Lean.
-- source:
--   Baez, Hoffnung, Rogers, Categorified Symplectic Geometry and the Classical String, arXiv:0808.0246v1, pp. 11–12, Proposition 3.6 part 1, equation (6)

import Mathlib
import Definitions.Def_CatSymplectic_Hemistrict_Basic

namespace CatSymplectic.Hemistrict

theorem proposition_3_6_1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (Ω : Form E 3) (hΩ : IsNPlectic 2 Ω)
    (F G : hamSubmodule Ω) :
    hemi Ω F G ∈ hamSubmodule Ω ∧
      IsHamVF Ω (hemi Ω F G)
        (VectorField.lieBracket ℝ (hamVF Ω F) (hamVF Ω G)) ∧
      hamVF Ω (hemi Ω F G) =
        VectorField.lieBracket ℝ (hamVF Ω F) (hamVF Ω G) := by sorry

end CatSymplectic.Hemistrict
