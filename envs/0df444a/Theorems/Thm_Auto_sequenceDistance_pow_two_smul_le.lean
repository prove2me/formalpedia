-- Prove2me | Theorems.Thm_Auto_sequenceDistance_pow_two_smul_le
-- name    : Auto.sequenceDistance_pow_two_smul_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:00:35.895529+00:00
-- url     : https://prove2.me/theorems/f90e5136-c0c7-473e-a46c-8035df8d50cf
-- title:
--   Auto: sequence Distance pow two smul le
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
--   `Auto.sequenceDistance_comm`,
--   `Auto.sequenceDistance_triangle`,
--   `Auto.sequenceDistance_shift_le`,
--   `Auto.sequenceDistance_smul`.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/MultiplicativelySpacedMonotoneSequences.lean#L672-L707
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/MultiplicativelySpacedMonotoneSequences.lean#L672-L707

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Preliminaries_MultiplicativelySpacedMonotoneSequences
set_option autoImplicit true
@[expose] public section
public section
open Auto
open Set

theorem Auto.sequenceDistance_pow_two_smul_le {a : ℤ → ℝ} (ha : SpacedSequence a) (h : ℤ) :
    SequenceDistance a (fun j => (2 : ℝ) ^ h * a j) ≤ (Int.natAbs h : WithTop ℕ) := by sorry
