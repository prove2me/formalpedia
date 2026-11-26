-- Prove2me | Theorems.Thm_Auto_max_mem_A
-- name    : Auto.max_mem_A
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:59:26.125026+00:00
-- url     : https://prove2.me/theorems/6458c2f1-6c79-44fa-8874-8c805a693924
-- title:
--   Auto: max mem A
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
--   See also `Auto.smul_mem_A`,
--   `Auto.shift_mem_A`,
--   `Auto.sqrt_sq_add_sq_mem_A`.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/MultiplicativelySpacedMonotoneSequences.lean#L225-L235
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/MultiplicativelySpacedMonotoneSequences.lean#L225-L235

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Preliminaries_MultiplicativelySpacedMonotoneSequences
set_option autoImplicit true
@[expose] public section
public section
open Auto
open Set

theorem Auto.max_mem_A {a b : ℤ → ℝ} (ha : SpacedSequence a) (hb : SpacedSequence b) :
    SpacedSequence (fun j => max (a j) (b j)) := by sorry
