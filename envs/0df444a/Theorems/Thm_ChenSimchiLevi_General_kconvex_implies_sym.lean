-- Prove2me | Theorems.Thm_ChenSimchiLevi_General_kconvex_implies_sym
-- name    : ChenSimchiLevi.General.kconvex_implies_sym
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T20:11:41.438144+00:00
-- url     : https://prove2.me/theorems/a4901261-1c72-4a29-87b3-710453f66f27
-- title:
--   $k$-convexity implies symmetric $k$-convexity
-- statement:
--   Every $k$-convex real function in the sense of Definition 2.1 is symmetrically $k$-convex in the sense of Definition 4.1:
--   $$\mathrm{KConvex}_k(f)\ \Longrightarrow\ \mathrm{SymKConvex}_k(f).$$
--   This connects the additive-demand analysis to the symmetric notion used for general demand.
-- source:
--   Chen, Simchi-Levi, Operations Research 52(6) (2004), p. 891, §4, sentence after Definition 4.1

import Definitions.Def_BertsekasKConvex
import Definitions.Def_ChenSimchiLevi_General_SymKConvex

set_option autoImplicit false

namespace ChenSimchiLevi.General

/-- §4, after Definition 4.1, p. 891. -/
theorem kconvex_implies_sym (k : ℝ) (f : ℝ → ℝ)
    (hf : BertsekasKConvex k f) : SymKConvex k f := by sorry

end ChenSimchiLevi.General
