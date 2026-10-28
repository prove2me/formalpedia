-- Prove2me | Theorems.Thm_D1Bound5_main_statement
-- name    : D1Bound5.main_statement
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T15:04:42.107575+00:00
-- url     : https://prove2.me/theorems/4bb5d407-713b-46ac-967d-97d7abf88598
-- title:
--   No Diophantine sextuples in imaginary quadratic integer rings
-- statement:
--   Let $K$ be an imaginary quadratic number field and let $\mathcal O_K$ be its full ring of integers. Let $A\subseteq\mathcal O_K\setminus\{0\}$ be finite. Suppose that, for every pair of distinct elements $a,b\in A$, there exists $r\in\mathcal O_K$ such that $r^2=ab+1$. Then
--   $$
--   |A|\le 5.
--   $$
--   Equivalently, no full ring of integers of an imaginary quadratic field contains a Diophantine sextuple. The bound is uniform over all imaginary quadratic fields, including $K=\mathbb Q(\sqrt{-d})$ with $d>0$ squarefree and $d\equiv3\pmod4$, for which $\mathcal O_K$ strictly contains $\mathbb Z[\sqrt{-d}]$. The case $ab+1=0$ is allowed, with $r=0$.
-- source:
--   Zrinka Franušić and Tomislav Pejković, A uniform bound of five for Diophantine tuples in imaginary quadratic integer rings, preprint, 2026, Theorem 1.1. Article and verification material: https://github.com/tomislav-math/diophantine-tuples-bound-five
--
--   Formal proposition D1Bound5.MainStatement in the canonical D1Bound5/Specification.lean file: https://github.com/tomislav-math/d1-bound5-lean/blob/1fe0adf1028af0e41ea578660c8d48875cde6588/D1Bound5/Specification.lean#L13-L16
--
--   Lean source repository: https://github.com/tomislav-math/d1-bound5-lean

import Definitions.Def_D1Bound5_MainStatement

open scoped NumberField
open Module

universe u

open D1Bound5

set_option autoImplicit false

theorem D1Bound5.main_statement : MainStatement.{u} := by sorry
