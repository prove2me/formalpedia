-- Prove2me | Theorems.Thm_Auto_shift_mem_A
-- name    : Auto.shift_mem_A
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:59:47.932567+00:00
-- url     : https://prove2.me/theorems/d3a0bed1-8977-4299-9f7f-028f5a13fac2
-- title:
--   Auto: shift mem A
-- statement:
--   **Proposition (Operations on spaced sequences).**
--
--   Let $a,b\in {\rm A}$. Then the following hold:
--
--   (i) $\max(a,b)\in {\rm A}$
--
--   (ii) $t\cdot a\in {\rm A}$ for every $t>0$.
--
--   (iii) Let $n\in\mathbb{Z}$. If $c:\mathbb{Z}\to(0,\infty)$ is defined by $c(j)=a(j+n)$ for all
--   $j\in\mathbb{Z}$, then $c\in {\rm A}$.
--
--   (iv) If $c:\mathbb{Z}\to (0,\infty)$ is defined by $c(j)=\sqrt{a(j)^2+b(j)^2}$ for all
--   $j\in\mathbb{Z}$, then $c\in {\rm A}$.
--
--   See also `Auto.max_mem_A`,
--   `Auto.smul_mem_A`,
--   `Auto.sqrt_sq_add_sq_mem_A`.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/MultiplicativelySpacedMonotoneSequences.lean#L284-L289
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/MultiplicativelySpacedMonotoneSequences.lean#L284-L289

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Preliminaries_MultiplicativelySpacedMonotoneSequences
set_option autoImplicit true
@[expose] public section
public section
open Auto
open Set

theorem Auto.shift_mem_A {a : ℤ → ℝ} (ha : SpacedSequence a) (n : ℤ) :
    SpacedSequence (fun j => a (j + n)) := by sorry
