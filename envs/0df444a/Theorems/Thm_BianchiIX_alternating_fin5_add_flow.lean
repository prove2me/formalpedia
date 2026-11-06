-- Prove2me | Theorems.Thm_BianchiIX_alternating_fin5_add_flow
-- name    : BianchiIX.alternating_fin5_add_flow
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T05:36:43.162204+00:00
-- url     : https://prove2.me/theorems/adda011a-9101-4c37-9bc6-5f9de748775f
-- title:
--   Flow-direction additions vanish in a fivefold alternating form
-- statement:
--   For a real vector space $E$, an alternating $5$-linear
--   form $f:E^5\to\mathbb R$, vectors $X,F,A,B,C$, and real $a,b,c$,
--   $$f(X,F,A+aF,B+bF,C+cF)=f(X,F,A,B,C).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/VolumeForms.lean#L44-L67

import Mathlib.LinearAlgebra.Determinant
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
variable {E ι : Type*} [AddCommGroup E] [Module ℝ E] [Fintype ι] [DecidableEq ι]

theorem BianchiIX.alternating_fin5_add_flow (f : E [⋀^Fin 5]→ₗ[ℝ] ℝ)
    (X F A B C : E) (a b c : ℝ) :
    f ![X, F, A + a • F, B + b • F, C + c • F] = f ![X, F, A, B, C] := by sorry
