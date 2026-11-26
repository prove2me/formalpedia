-- Prove2me | Theorems.Thm_Eden_real_subadditive_eventually_div_lt
-- name    : Eden.real_subadditive_eventually_div_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:39:33.527416+00:00
-- url     : https://prove2.me/theorems/093f75cf-2059-576d-aeb9-381252f8e322
-- title:
--   Eden: real subadditive eventually div lt
-- statement:
--   The Eden construction uses the real subadditive eventually div lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/RealSubadditive.lean#L65-L78
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/RealSubadditive.lean#L65-L78

import Definitions.Def_Eden_GlobalGrowth
import Mathlib.Analysis.Subadditive
import Mathlib.Algebra.Order.Floor.Semiring
import Definitions.Def_Eden_RealSubadditive
set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden

theorem Eden.real_subadditive_eventually_div_lt {f : ℝ → ℝ} {C : ℝ}
    (hsub : ∀ s t, 0 ≤ s → 0 ≤ t → f (s + t) ≤ f s + f t)
    (hC : 0 ≤ C) (hbound : ∀ t, 0 ≤ t → |f t| ≤ C * t)
    {T L : ℝ} (hT : 0 < T) (hL : f T / T < L) :
    ∀ᶠ t : ℝ in atTop, f t / t < L := by sorry
