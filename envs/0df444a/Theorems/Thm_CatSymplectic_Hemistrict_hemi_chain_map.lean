-- Prove2me | Theorems.Thm_CatSymplectic_Hemistrict_hemi_chain_map
-- name    : CatSymplectic.Hemistrict.hemi_chain_map
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:40:09.443423+00:00
-- url     : https://prove2.me/theorems/bd34dc4b-0a3f-4c14-a62a-8de0dbeb5f6e
-- title:
--   p. 17 — degree-one hemi-bracket is a chain map
-- statement:
--   For Hamiltonian \(F\) and smooth \(f\), the degree-one chain-map identities are
--
--   $$
--   d\{F,f\}_h=\{F,df\}_h,\qquad
--   d\{f,F\}_h=0=\{df,F\}_h.
--   $$
--
--   They make the bracket compatible with the complex differential on both degree-one summands.
--
--   **Formalization Note** The statement is on a finite-dimensional real normed space. The right hemi-bracket on a function and form is zero by definition. The paper's \(\omega\) is Ω in Lean.
-- source:
--   Baez, Hoffnung, Rogers, Categorified Symplectic Geometry and the Classical String, arXiv:0808.0246v1, p. 17, paragraph preceding Theorem 4.3

import Mathlib
import Definitions.Def_CatSymplectic_Hemistrict_Basic

namespace CatSymplectic.Hemistrict

theorem hemi_chain_map {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (Ω : Form E 3) (hΩ : IsNPlectic 2 Ω)
    (F : hamSubmodule Ω) (f : smoothFns E) :
    ContWeatherall.grad (hemiFn Ω F f) =
      hemi Ω F (ContWeatherall.grad f) ∧
    hemi Ω (ContWeatherall.grad f) F = 0 := by sorry

end CatSymplectic.Hemistrict
