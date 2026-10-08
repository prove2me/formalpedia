-- Prove2me | Theorems.Thm_ContactCalculus_exterior_pairing_pullback
-- name    : ContactCalculus.exterior_pairing_pullback
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-07T16:34:55.339841+00:00
-- url     : https://prove2.me/theorems/8821a7f1-64d7-419d-ad64-3a1c4efb77aa
-- title:
--   Exterior pairing is natural under a C² pullback
-- statement:
--   Let V and W be real normed vector spaces, let alpha be a covector-valued function on W differentiable at g(x), and let g from V to W be C squared at x. Define the pulled-back covector by
--
--   $$P(z)=\alpha(g(z))\circ Dg_z.$$
--
--   For every pair of vectors u and v in V,
--
--   $$DP_x(u)(v)-DP_x(v)(u)=D\alpha_{g(x)}(Dg_xu)(Dg_xv)-D\alpha_{g(x)}(Dg_xv)(Dg_xu).$$
--
--   This is exterior-derivative naturality expressed directly in terms of covectors and Frechet derivatives. Neither finite-dimensionality nor completeness of the spaces is required.
-- source:
--   Naturality of exterior differentiation. Mathlib 0df444a360eaa60ab8c11dca51a86af692955474, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean, extDeriv_pullback; covector specialization proved using fderiv_clm_comp and ContDiffAt.isSymmSndFDerivAt in FDeriv/Symmetric.lean.

import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.Ring

set_option autoImplicit false
open scoped ContDiff

theorem ContactCalculus.exterior_pairing_pullback
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (α : W → W →L[ℝ] ℝ) (g : V → W) (x u v : V)
    (hα : DifferentiableAt ℝ α (g x)) (hg : ContDiffAt ℝ 2 g x) :
    fderiv ℝ (fun z => (α (g z)).comp (fderiv ℝ g z)) x u v -
      fderiv ℝ (fun z => (α (g z)).comp (fderiv ℝ g z)) x v u =
    fderiv ℝ α (g x) (fderiv ℝ g x u) (fderiv ℝ g x v) -
      fderiv ℝ α (g x) (fderiv ℝ g x v) (fderiv ℝ g x u) := by sorry
