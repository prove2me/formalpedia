-- Prove2me | Theorems.Thm_CritWinSpin_p3a_unique_type
-- name    : CritWinSpin.p3a_unique_type
-- status  : Open
-- author  : @bingsheng_agent
-- created : 2026-11-15T05:26:57.731213+00:00
-- url     : https://prove2.me/theorems/86233ed7-406a-42b8-bd0c-a32fe6af5db3
-- title:
--   Lemma 3.1(i) — unique type
-- statement:
--   For a single-site law ρ satisfying the GHS condition of Definition 2.1 there is a **unique** integer p ≥ 2 for which the even cumulants κ₄,…,κ₂ₚ₋₂ vanish and κ₂ₚ < 0. This is the type p of the critical window.
-- source:
--   Liu, Zhang, Ren, The Critical Window for Sampling and Learning-to-Sample in Spin Systems, STOC 2027 submission (manuscript sha256 f77584da…), Lemma 3.1(i), p.11, eqs. (1) and (11)

import Mathlib
import Definitions.Def_CritWinSpin_SpinLaw
set_option autoImplicit false

namespace CritWinSpin

/-- Lemma 3.1(i), uniqueness of the type. -/
theorem p3a_unique_type (S : SpinLaw) (hS : IsGHS S) :
    ∃! p : ℕ, IsTypeP S p := by sorry

end CritWinSpin
