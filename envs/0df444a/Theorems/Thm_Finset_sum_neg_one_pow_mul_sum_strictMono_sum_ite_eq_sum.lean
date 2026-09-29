-- Prove2me | Theorems.Thm_Finset_sum_neg_one_pow_mul_sum_strictMono_sum_ite_eq_sum
-- name    : Finset.sum_neg_one_pow_mul_sum_strictMono_sum_ite_eq_sum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/83068d48-4136-54be-8959-a4da628894fd
-- title:
--   Alternating sum over ordered chains recovers the total sum
-- statement:
--   Let $\iota$ be a finite type equipped with a linear order, let $\beta$ be a type, let $T$ be a finite subset of $\beta$ and $a : \beta \to \mathbb{Z}$ a weight function. Let $\mathrm{mem} : \iota \to \beta \to \mathrm{Prop}$ be an arbitrary relation, thought of as assigning to each $i \in \iota$ the set $V_i = \{y : \mathrm{mem}\ i\ y\}$, and assume the covering hypothesis that every $y \in T$ satisfies $\mathrm{mem}\ i\ y$ for at least one $i$. Let $N$ be a natural number with $\mathrm{card}\,\iota \le N$. For each $p$, indexing is by the type of strictly monotone maps $s : \mathrm{Fin}(p+1) \to \iota$, i.e. chains $s(0) < \cdots < s(p)$ in $\iota$. The assertion is the identity in $\mathbb{Z}$
--   $$\sum_{p < N} (-1)^p \sum_{s\ \text{strictly monotone}} \ \sum_{y \in T} \bigl[\,\text{if } \mathrm{mem}\ (s(j))\ y \text{ for all } j \text{ then } a(y) \text{ else } 0\,\bigr] \;=\; \sum_{y \in T} a(y),$$
--   that is, the alternating sum over chains of the weights of the points lying in all of $V_{s(0)},\dots,V_{s(p)}$ equals the total weight of $T$.
--
--   This is the combinatorial inclusion–exclusion identity underlying the alternating-sum formula for a Čech-type computation with respect to a finite ordered cover: the contributions of the intersections indexed by increasing chains telescope to the total. It is used in the computation of an Euler characteristic as an alternating sum of lengths over an ordered cover, in [`AlgebraicGeometry.Polarisation.eulerChar_mumfordBundle_tensor_pullback_snd_eq_sum_alternating_length_of_forall_mem`](thm.html#AlgebraicGeometry.Polarisation.eulerChar_mumfordBundle_tensor_pullback_snd_eq_sum_alternating_length_of_forall_mem).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Finset_sum_neg_one_pow_mul_sum_strictMono_sum_ite_eq_sum.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open Classical in

theorem Finset.sum_neg_one_pow_mul_sum_strictMono_sum_ite_eq_sum
    {ι : Type u} [Fintype ι] [LinearOrder ι] {β : Type v} (T : Finset β) (a : β → ℤ)
    (mem : ι → β → Prop) (hcov : ∀ y ∈ T, ∃ i, mem i y) (N : ℕ) (hN : Fintype.card ι ≤ N) :
    ∑ p ∈ Finset.range N, (-1 : ℤ) ^ p *
        ∑ s : {s : Fin (p + 1) → ι // StrictMono s}, ∑ y ∈ T, (if ∀ j, mem (s.1 j) y then a y else 0) =
      ∑ y ∈ T, a y := by sorry
