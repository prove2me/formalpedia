-- Prove2me | Theorems.Thm_Auto_sequenceDistance_comm
-- name    : Auto.sequenceDistance_comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:00:09.915332+00:00
-- url     : https://prove2.me/theorems/a24a5f2b-7774-57aa-80b3-97c685cb7abe
-- title:
--   Auto: sequence Distance comm
-- statement:
--   **Proposition (Properties of distance of sequences).**
--
--   Let $a,b,c\in {\rm A}$.
--   Then
--
--   (i) If $\operatorname{dist}(a,b)=0$, then $a=b$.
--
--   (ii) $\operatorname{dist}(a,b)=\operatorname{dist}(b,a)$
--
--   (iii) $\operatorname{dist}(a,c)\le \operatorname{dist}(a,b)+\operatorname{dist}(b,c)$
--
--   (iv) If $c(j)=b(j+1)$, then $\operatorname{dist}(a,c)\le \operatorname{dist}(a,b)+1$.
--
--   (v) For all $t>0$, $\operatorname{dist}(t\cdot a,t\cdot b)=\operatorname{dist}(a,b)$
--
--   (vi) For all $h\in\mathbb{Z}$,
--   $\operatorname{dist}(a,2^h a)\le |h|$.
--
--   See also `Auto.sequenceDistance_zero_eq`,
--   `Auto.sequenceDistance_triangle`,
--   `Auto.sequenceDistance_shift_le`,
--   `Auto.sequenceDistance_smul`,
--   `Auto.sequenceDistance_pow_two_smul_le`.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/MultiplicativelySpacedMonotoneSequences.lean#L481-L499
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/MultiplicativelySpacedMonotoneSequences.lean#L481-L499

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Preliminaries_MultiplicativelySpacedMonotoneSequences
set_option autoImplicit true
@[expose] public section
public section
open Auto
open Set

theorem Auto.sequenceDistance_comm (a b : ℤ → ℝ) :
    SequenceDistance a b = SequenceDistance b a := by sorry
