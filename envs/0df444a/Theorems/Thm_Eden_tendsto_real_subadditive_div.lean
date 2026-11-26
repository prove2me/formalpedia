-- Prove2me | Theorems.Thm_Eden_tendsto_real_subadditive_div
-- name    : Eden.tendsto_real_subadditive_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:39:36.160359+00:00
-- url     : https://prove2.me/theorems/46bdc5cd-eac1-5b3c-88e7-6d2067f5bde5
-- title:
--   Eden: tendsto real subadditive div
-- statement:
--   Fekete's formula through all real times, with an explicit linear bound.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/RealSubadditive.lean#L81-L98
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/RealSubadditive.lean#L81-L98

import Definitions.Def_Eden_GlobalGrowth
import Mathlib.Analysis.Subadditive
import Mathlib.Algebra.Order.Floor.Semiring
import Definitions.Def_Eden_RealSubadditive
set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden

theorem Eden.tendsto_real_subadditive_div {f : ℝ → ℝ} {C : ℝ}
    (hsub : ∀ s t, 0 ≤ s → 0 ≤ t → f (s + t) ≤ f s + f t)
    (hC : 0 ≤ C) (hbound : ∀ t, 0 ≤ t → |f t| ≤ C * t) :
    Tendsto (fun t : ℝ => f t / t) atTop
      (𝓝 (sInf ((fun T : ℝ => f T / T) '' Ioi 0))) := by sorry
