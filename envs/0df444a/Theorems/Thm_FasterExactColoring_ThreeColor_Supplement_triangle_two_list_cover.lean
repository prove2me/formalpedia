-- Prove2me | Theorems.Thm_FasterExactColoring_ThreeColor_Supplement_triangle_two_list_cover
-- name    : FasterExactColoring.ThreeColor.Supplement.triangle_two_list_cover
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:52:55.121293+00:00
-- url     : https://prove2.me/theorems/08354817-66e1-4400-82e4-a517085d5b8f
-- title:
--   Lemma 5.3 (used in the proof of Theorem 1.3) — constructive triangle two-list cover
-- statement:
--   For every nonnegative integer $n$, let $V$ be the vertices of $n$ pairwise disjoint triangles. There is one deterministic finite program constructing and enumerating a finite family $\mathcal L_n$ of assignments of a two-element color list to every vertex. For every proper coloring $\varphi:V\to[4]$ that uses color $4$ on each triangle, some $L\in\mathcal L_n$ satisfies $\varphi(v)\in L(v)$ for every vertex. With $m=\lceil\ln(n+2)\rceil$, $b=\lceil n/m\rceil$, and $h(0)=0$, $h(n)=b\ln(m\ln18+1)$ for $n>0$,
--   $$|\mathcal L_n|\le(9/2)^n e^{h(n)},\qquad h(n)=o(n).$$
--   The same program outputs the whole family, without repetitions, in charged time at most $C(n+1)^d(|\mathcal L_n|+1)$ for fixed $C>0,d\in\mathbb N$. Every list has exactly two colors. At $n=0$ this is the singleton family of the empty assignment. This is the deterministic covering tool needed for the CSP terminal bound.
--
--   Differences from the source:
--   - encoding: arbitrary vertex labels on disjoint triangles, with size (9/2)^n exp(o(n)) → canonical labels Fin n times Fin 3, duplicate-free encoded families and the explicit block envelope h; reason: finite relabeling changes no coloring or list; the proof supplies this same envelope and its sublinearity, and charged total enumeration implies the stated O* bound
-- source:
--   Ryosuke Yamano, Tetsuo Shibuya, STOC 2027 submission #727 (October 2026), Lemma 5.3, p. 11 (PDF p. 13)

import Mathlib
import Definitions.Def_FasterExactColoring_ThreeColor_Supplement_TriangleLists

set_option autoImplicit false

namespace FasterExactColoring.ThreeColor.Supplement

theorem triangle_two_list_cover :
  sublinear coverEnvelope ∧
  ∃ (A : Program) (C : ℝ) (d : ℕ), 0 < C ∧ deterministic A ∧
    ∀ n : ℕ, ∃ F : List (TwoLists n),
      F.Nodup ∧ (∀ L ∈ F, twoListsValid L) ∧
      (∀ f : TriangleVertex n → Fin 4, triangleColoring f → ∃ L ∈ F, compatible f L) ∧
      (F.length : ℝ) ≤ (9/2 : ℝ)^n * Real.exp (coverEnvelope n) ∧
      runWithin A [n] (C*(n+1 : ℕ)^d*(F.length+1 : ℕ))
        (fun y => y = triangleFamilyCode F) := by sorry

end FasterExactColoring.ThreeColor.Supplement
