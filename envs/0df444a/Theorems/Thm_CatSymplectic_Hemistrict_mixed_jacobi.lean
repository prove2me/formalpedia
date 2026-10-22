-- Prove2me | Theorems.Thm_CatSymplectic_Hemistrict_mixed_jacobi
-- name    : CatSymplectic.Hemistrict.mixed_jacobi
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:40:02.988315+00:00
-- url     : https://prove2.me/theorems/a1527513-1635-4a38-bbc7-fdc222f9a0dc
-- title:
--   proof of Theorem 4.3, p. 17 — mixed Jacobi identity
-- statement:
--   For Hamiltonian one-forms \(F,G\) and a smooth function \(f\), the Jacobi equation with one degree-one input is
--
--   $$
--   \{F,\{G,f\}_h\}_h
--   =\{\{F,G\}_h,f\}_h+\{G,\{F,f\}_h\}_h.
--   $$
--
--   It supplies the nonzero mixed-degree component of the identity Jacobiator.
--
--   **Formalization Note** The objects are globally smooth on a finite-dimensional real normed space. The paper's \(\omega\) is Ω in Lean.
-- source:
--   Baez, Hoffnung, Rogers, Categorified Symplectic Geometry and the Classical String, arXiv:0808.0246v1, p. 17, proof of Theorem 4.3, first mixed Jacobi display

import Mathlib
import Definitions.Def_CatSymplectic_Hemistrict_Basic

namespace CatSymplectic.Hemistrict

theorem mixed_jacobi {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (Ω : Form E 3) (hΩ : IsNPlectic 2 Ω)
    (F G : hamSubmodule Ω) (f : smoothFns E) :
    hemiFn Ω F (hemiFn Ω G f) =
      hemiFn Ω (hemi Ω F G) f + hemiFn Ω G (hemiFn Ω F f) := by sorry

end CatSymplectic.Hemistrict
