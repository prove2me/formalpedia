-- Prove2me | Theorems.Thm_AnonymousDirectedCounting_Exact_Supplement_exact_cover_equation
-- name    : AnonymousDirectedCounting.Exact.Supplement.exact_cover_equation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:56:55.493096+00:00
-- url     : https://prove2.me/theorems/13f36b9c-2d6e-43c9-912e-63eadd37f9a4
-- title:
--   Lemma 14 — the base-B equation and exact covers
-- statement:
--   Let $q\ge2$ and let $S_1,\dots,S_m$ be distinct three-element subsets of $\{0,\dots,3q-1\}$, with $B,K,W,A,c_0,\dots,c_m$ as in Appendix F.1. For nonnegative integers $x_0,\dots,x_m$ consider
--   $$Ax_0+\sum_{j=1}^mc_jx_j=A.\tag{5}$$
--   1. The reference solution $x_0=1$, $x_1=\dots=x_m=0$ satisfies (5).
--   2. Every other solution has $x_0=0$, every $x_j\in\{0,1\}$, and the triples $S_j$ with $x_j\ne0$ form an exact cover.
--   3. Conversely, every exact cover $J$ gives the solution $x_0=0$, $x_j=\mathbf 1[j\in J]$.
--   4. Every solution satisfies $\sum_{i=0}^mx_i\le q$.
--
--   The lemma translates exact covers into the alternative group sizes of the reduction.
--
--   Differences from the source:
--   - encoding: triples S_1..S_m and coordinates x_0..x_m → S : Fin m → Finset ℕ and x : Fin (m + 1) → ℕ with group j + 1 for triple j; (5) written ∑_i c_i x_i = A with c_0 = A; reason: same equation
--   - reading: its nonzero coordinates x_j select an exact cover → every x_j ≤ 1 and {j : x_j ≠ 0} is an exact cover; reason: selecting triples is 0/1 selection; the proof states that each x_j is zero or one
--   - encoding: an exact cover consists of q triples containing each element exactly once → every element of U lies in exactly one selected triple; reason: with triples of size 3 inside U this forces exactly q triples
-- source:
--   Giuseppe A. Di Luna, Giovanni Viglietta, STOC 2027 submission #455 (October 2026), printed p. 28 (PDF p. 30), Lemma 14

import Mathlib
import Definitions.Def_AnonymousDirectedCounting_Exact_Supplement_X3CReduction

set_option autoImplicit false

open AnonymousDirectedCounting.Exact

namespace AnonymousDirectedCounting.Exact.Supplement

/-- Lemma 14, printed p. 28 (PDF p. 30). For nonnegative integers `x_0, …, x_m`, equation (5),
`A x_0 + ∑_{j=1}^m c_j x_j = A`, written `∑_i c_i x_i = A` with `c_0 = A`, has the reference solution
`x_0 = 1`, `x_j = 0`; every other solution has `x_0 = 0`, coordinates `x_j ∈ {0, 1}`, and its nonzero
coordinates select an exact cover; every exact cover gives such a solution; and every solution has
`∑_{i=0}^m x_i ≤ q`. -/
theorem exact_cover_equation (q m : ℕ) (S : Fin m → Finset ℕ) (hS : IsX3CInstance q m S) :
    (∑ i, coef q m S i * (if i = 0 then 1 else 0) = coefA q) ∧
    (∀ x : Fin (m + 1) → ℕ, ∑ i, coef q m S i * x i = coefA q →
      x ≠ (fun i => if i = 0 then 1 else 0) →
        x 0 = 0 ∧ (∀ j : Fin m, x j.succ ≤ 1) ∧
          IsExactCover q m S (Finset.univ.filter (fun j : Fin m => x j.succ ≠ 0))) ∧
    (∀ J : Finset (Fin m), IsExactCover q m S J →
      ∑ i, coef q m S i * (Fin.cases 0 (fun j => if j ∈ J then 1 else 0) : Fin (m + 1) → ℕ) i =
        coefA q) ∧
    (∀ x : Fin (m + 1) → ℕ, ∑ i, coef q m S i * x i = coefA q → ∑ i, x i ≤ q) := by sorry

end AnonymousDirectedCounting.Exact.Supplement
