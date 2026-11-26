-- Prove2me | Theorems.Thm_Eden_real_subadditive_mul_add_le
-- name    : Eden.real_subadditive_mul_add_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:39:18.40375+00:00
-- url     : https://prove2.me/theorems/a837a583-b9e9-5abd-9c23-9f9228cec6e6
-- title:
--   Eden: real subadditive mul add le
-- statement:
--   The Eden construction uses the real subadditive mul add le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/RealSubadditive.lean#L17-L32
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/RealSubadditive.lean#L17-L32

import Definitions.Def_Eden_GlobalGrowth
import Mathlib.Analysis.Subadditive
import Mathlib.Algebra.Order.Floor.Semiring
import Definitions.Def_Eden_RealSubadditive
set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden

theorem Eden.real_subadditive_mul_add_le {f : ℝ → ℝ}
    (hsub : ∀ s t, 0 ≤ s → 0 ≤ t → f (s + t) ≤ f s + f t)
    {T r : ℝ} (hT : 0 ≤ T) (hr : 0 ≤ r) (m : ℕ) :
    f ((m : ℝ) * T + r) ≤ (m : ℝ) * f T + f r := by sorry
