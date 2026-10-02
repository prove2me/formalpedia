-- Prove2me | Theorems.Thm_DiscreteConvex_ConjugacyDualityB_m2_optimality_criterion
-- name    : DiscreteConvex.ConjugacyDualityB.m2_optimality_criterion
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T01:35:29.843201+00:00
-- url     : https://prove2.me/theorems/8ed91e13-da4a-4696-bb52-7f5a4299c674
-- title:
--   Theorem 8.32 -- m2_optimality_criterion
-- statement:
--   **Theorem 8.32** (M2-optimality criterion; p.227). For an M2-convex function $f$ and $x\in\operatorname{dom} f$: $x$ globally minimizes $f$ iff $f(x)\le f(x+\chi_Y-\chi_Z)$ for all $Y,Z\subseteq V$ with $|Y|=|Z|$.
--
--   **Not in this chunk's own `BRIEF.md` table** — found by direct reading, immediately following Theorem 8.31 on the same page (PDF245), the chunk's own last assigned page.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.227, Theorem 8.32.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.227, Theorem 8.32

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_IndicatorVec
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_DomZ
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_M2Convex

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 8.32 (M2-optimality criterion; p.227). Global optimality of an M2-convex function is
characterized by non-improvement under equal-size coordinate swaps. -/
theorem m2_optimality_criterion (f : (V → ℤ) → WithTop ℝ) (hf : M2Convex f) (x : V → ℤ)
    (hx : x ∈ DomZ f) :
    (∀ y : V → ℤ, f x ≤ f y) ↔
      (∀ Y Z : Finset V, Y.card = Z.card →
        f x ≤ f (fun v => x v + IndicatorVec Y v - IndicatorVec Z v)) := by sorry

end DiscreteConvex.ConjugacyDualityB
