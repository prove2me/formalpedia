-- Prove2me | Theorems.Thm_Finsupp_exists_eq_sum_single_of_mapDomain_eq_sum_single
-- name    : Finsupp.exists_eq_sum_single_of_mapDomain_eq_sum_single
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/cc2c02ab-7628-5750-981a-9ba07371a00a
-- title:
--   Effective ℤ-divisor pushing forward to a reduced sum
-- statement:
--   Let $\alpha$ and $\beta$ be types, $f \colon \alpha \to \beta$ a map, and $E \colon \alpha \to_0 \mathbb{Z}$ a finitely supported function with $0 \le E$, that is, $E(a) \ge 0$ for every $a$ (the pointwise order on $\alpha \to_0 \mathbb{Z}$). Let $d$ be a natural number and $v \colon \mathrm{Fin}\, d \to \beta$ an injective family, so the points $v_i$ are pairwise distinct. Assume that the pushforward of $E$ along $f$, given by `Finsupp.mapDomain f E` (the function sending $b$ to the sum of $E(a)$ over $a$ with $f(a) = b$), equals the reduced sum $\sum_{i} \mathrm{single}(v_i, 1)$, the finitely supported function taking the value $1$ at each $v_i$ and $0$ elsewhere. The conclusion is that there exists a family $Q \colon \mathrm{Fin}\, d \to \alpha$ with $E = \sum_{i} \mathrm{single}(Q_i, 1)$ and $f(Q_i) = v_i$ for every $i$; thus $E$ is itself a reduced sum of $d$ points, one lying in each fibre $f^{-1}(v_i)$.
--
--   This is the fibre decomposition of an effective cycle over a reduced image: an effective divisor whose pushforward is a reduced divisor of the same degree has exactly one point, of multiplicity one, in each fibre. It is used in the analysis of prolongation data on modular curves, to convert an effective divisor whose reduction is a prescribed reduced divisor into a family of points indexed in the same way as that reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Finsupp_exists_eq_sum_single_of_mapDomain_eq_sum_single.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Finsupp.exists_eq_sum_single_of_mapDomain_eq_sum_single
    {α β : Type*} (f : α → β) (E : α →₀ ℤ) (hE : 0 ≤ E)
    {d : ℕ} (v : Fin d → β) (hv : Function.Injective v)
    (h : Finsupp.mapDomain f E = ∑ i, Finsupp.single (v i) (1 : ℤ)) :
    ∃ Q : Fin d → α, E = ∑ i, Finsupp.single (Q i) (1 : ℤ) ∧ ∀ i, f (Q i) = v i := by sorry
