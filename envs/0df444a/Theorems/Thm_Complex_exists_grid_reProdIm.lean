-- Prove2me | Theorems.Thm_Complex_exists_grid_reProdIm
-- name    : Complex.exists_grid_reProdIm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/ace3e448-b983-5522-aa5e-c382e0836b81
-- title:
--   Finite δ-net of a complex rectangle with short δ-chains
-- statement:
--   Let $a_1,a_2,b_1,b_2,\delta$ be real numbers with $a_1\le a_2$, $b_1\le b_2$ and $\delta>0$, and let $R = \mathrm{Icc}\,a_1\,a_2 \times_{\mathbb C} \mathrm{Icc}\,b_1\,b_2$ be the closed rectangle in $\mathbb C$ consisting of the $w$ with $\operatorname{Re} w \in [a_1,a_2]$ and $\operatorname{Im} w \in [b_1,b_2]$. The assertion is that there exist natural numbers $m,n$ and a family $c \colon \mathrm{Fin}(m+1) \times \mathrm{Fin}(n+1) \to \mathbb C$ of points with three properties: first, $c\,i \in R$ for every index $i$; second, every $w \in R$ satisfies $\operatorname{dist}(w, c\,i) < \delta$ for at least one index $i$, so the $c\,i$ form a finite $\delta$-net of $R$; third, for any two indices $i,j$ there are a length $L \in \mathbb N$ and a function $\pi \colon \mathbb N \to \mathrm{Fin}(m+1) \times \mathrm{Fin}(n+1)$ with $L \le m+n$, $\pi\,0 = i$, $\pi\,L = j$, and $\operatorname{dist}(c(\pi\,l), c(\pi\,(l+1))) \le \delta$ for every $l < L$. The chain $\pi$ is indexed by all of $\mathbb N$, only its values at $l \le L$ being constrained; the single parameter $\delta$ serves both as covering radius and as bound on the step length.
--
--   This is the combinatorial skeleton of a Harnack chain on a compact rectangle: a finite $\delta$-net of centres together with, between any two of them, a chain of uniformly bounded length whose consecutive members are $\delta$-close. It is used in the analysis on the modular curve, in [`ModularCurve.JZero.exists_hyperplaneSection_sum_log_secVal_ge`](thm.html#ModularCurve.JZero.exists_hyperplaneSection_sum_log_secVal_ge), to propagate a bound from one point of a truncated fundamental region to all of it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Complex_exists_grid_reProdIm.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Complex.exists_grid_reProdIm {a₁ a₂ b₁ b₂ δ : ℝ} (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) (hδ : 0 < δ) :
    ∃ (m n : ℕ) (c : Fin (m + 1) × Fin (n + 1) → ℂ),
      (∀ i, c i ∈ Set.Icc a₁ a₂ ×ℂ Set.Icc b₁ b₂) ∧
      (∀ w ∈ Set.Icc a₁ a₂ ×ℂ Set.Icc b₁ b₂, ∃ i, dist w (c i) < δ) ∧
      (∀ i j, ∃ (L : ℕ) (π : ℕ → Fin (m + 1) × Fin (n + 1)),
        L ≤ m + n ∧ π 0 = i ∧ π L = j ∧ ∀ l < L, dist (c (π l)) (c (π (l + 1))) ≤ δ) := by sorry
