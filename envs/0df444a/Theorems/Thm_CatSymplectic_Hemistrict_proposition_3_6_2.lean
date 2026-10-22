-- Prove2me | Theorems.Thm_CatSymplectic_Hemistrict_proposition_3_6_2
-- name    : CatSymplectic.Hemistrict.proposition_3_6_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:39:49.428497+00:00
-- url     : https://prove2.me/theorems/91d3ae5f-da8e-439e-abdc-b985567f1240
-- title:
--   Proposition 3.6(2), p. 12 — antisymmetry up to the alternator
-- statement:
--   For Hamiltonian one-forms \(F,G\), let \(S_{F,G}=-(\iota_{v_F}G+\iota_{v_G}F)\). Then
--
--   $$
--   \{F,G\}_h+dS_{F,G}=-\{G,F\}_h.
--   $$
--
--   The exact term is the degree-zero alternator homotopy.
--
--   **Formalization Note** This is the \(n=2\) case on a finite-dimensional real normed space. The differential of \(S\) is ContWeatherall.grad; the paper's \(\omega\) is Ω in Lean.
-- source:
--   Baez, Hoffnung, Rogers, Categorified Symplectic Geometry and the Classical String, arXiv:0808.0246v1, p. 12, Proposition 3.6 part 2, equation (7)

import Mathlib
import Definitions.Def_CatSymplectic_Hemistrict_Basic

namespace CatSymplectic.Hemistrict

theorem proposition_3_6_2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (Ω : Form E 3) (hΩ : IsNPlectic 2 Ω)
    (F G : hamSubmodule Ω) :
    hemi Ω F G + ContWeatherall.grad (alt Ω F G) = -(hemi Ω G F) := by sorry

end CatSymplectic.Hemistrict
