-- Prove2me | Theorems.Thm_BFVBound_F_le_self
-- name    : BFVBound.F_le_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-02T15:41:14.369246+00:00
-- url     : https://prove2.me/theorems/3cfa3eff-b02c-401a-a1d0-7fe74f188d38
-- title:
--   Product-side bound, positive range: $F(s)\\le s$ on $[0,1/3]$
-- statement:
--   **Upper bound on the product expectation in the positive range.**
--
--   Let $F(s)=\frac{8}{3\pi}s\,G(s^{2})$ be the expected correlation of the BFV/GP product rounding at Pauli
--   correlation $s$. Then for $s\in[0,\tfrac13]$,
--   $$F(s)\ \le\ s .$$
--   Indeed $G(s^2)\le\frac{1}{1-s^2}\le\frac98$ (the geometric domination of `G_le_geom`, and $s^2\le\tfrac19$),
--   while $\frac{8}{3\pi}\le\frac89$ because $\pi\ge3$; multiplying gives
--   $F(s)\le\frac89\cdot\frac98\cdot s=s$. The inequality is what lets a per-edge mixture bound be turned into a
--   *linear* constraint in $s$ on the positive range: there the product side is the only active term.
-- source:
--   Anshu, Lee, Mousavi, Parekh, Soleimanifar, arXiv:2504.15276 Section 4.2 Eq. (17); Parekh-Thompson arXiv:2110.07781 Eq. (3); Brandao-Fernandes-Vallentin arXiv:0910.5765; G = 2F1(1/2,1/2;2;.) is the hypergeometric factor of the rank-three product rounding.

import Mathlib
import Definitions.Def_QuantumMaxCutBFVProductRounding
open scoped BigOperators

namespace BFVBound

theorem F_le_self (s : ℝ) (h0 : 0 ≤ s) (h1 : s ≤ 1 / 3) : F s ≤ s := by sorry

end BFVBound
