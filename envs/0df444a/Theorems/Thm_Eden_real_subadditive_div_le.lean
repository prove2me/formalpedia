-- Prove2me | Theorems.Thm_Eden_real_subadditive_div_le
-- name    : Eden.real_subadditive_div_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:39:22.054529+00:00
-- url     : https://prove2.me/theorems/30ef09c4-c41d-5e9e-9dca-6fc058d820a3
-- title:
--   Eden: real subadditive div le
-- statement:
--   The comparison estimate covers all positive real times, including t<T.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/RealSubadditive.lean#L35-L63
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/RealSubadditive.lean#L35-L63

import Definitions.Def_Eden_GlobalGrowth
import Mathlib.Analysis.Subadditive
import Mathlib.Algebra.Order.Floor.Semiring
import Definitions.Def_Eden_RealSubadditive
set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden

theorem Eden.real_subadditive_div_le {f : ℝ → ℝ} {C : ℝ}
    (hsub : ∀ s t, 0 ≤ s → 0 ≤ t → f (s + t) ≤ f s + f t)
    (hC : 0 ≤ C) (hbound : ∀ t, 0 ≤ t → |f t| ≤ C * t)
    {T t : ℝ} (hT : 0 < T) (ht : 0 < t) :
    f t / t ≤ f T / T + (C + |f T / T|) * T / t := by sorry
