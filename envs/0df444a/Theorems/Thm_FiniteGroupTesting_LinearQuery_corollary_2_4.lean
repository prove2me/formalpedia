-- Prove2me | Theorems.Thm_FiniteGroupTesting_LinearQuery_corollary_2_4
-- name    : FiniteGroupTesting.LinearQuery.corollary_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:03:17.790028+00:00
-- url     : https://prove2.me/theorems/cbec6079-2fdb-4d5f-97d1-a83a69b9544e
-- title:
--   Corollary 2.4 — short random generators
-- statement:
--   There are absolute $c_0,c_1>0$, chosen before every finite group $H$ of order $n$, such that for $k=\lceil c_0\log n\rceil$ independent uniform samples,
--
--   $$\Pr\left[\forall x\in H,\ \exists\text{ a word for }x\text{ in sampled elements and inverses of length}\le c_1\log n\right]\ge\frac23.$$
--
--   The event provides words for all elements simultaneously. Words retain arbitrary repetitions; the empty word covers the singleton case $n=1,k=0$. This is the source result at its exact constants' existential strength, independent of the later integer implementation choices.
--
--   Differences from the source: none.
-- source:
--   Nader Bshouty, STOC 2027 submission #622 (October 2026), p. 14, Corollary 2.4

import Definitions.Def_FiniteGroupTesting_LinearQuery_RandomCayley

set_option autoImplicit false

namespace FiniteGroupTesting.LinearQuery

/-- Corollary 2.4, p. 14: absolute constants and simultaneous words for all elements. -/
theorem corollary_2_4 :
    ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧ ∀ (H : Type) [Group H] [Fintype H],
      (2/3 : ℝ) ≤ uniformProbability
        (fun a : Fin ⌈c₀ * Real.log (Fintype.card H)⌉₊ → H =>
          ShortWords a (c₁ * Real.log (Fintype.card H))) := by sorry

end FiniteGroupTesting.LinearQuery
