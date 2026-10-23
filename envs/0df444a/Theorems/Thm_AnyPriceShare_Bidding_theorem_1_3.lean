-- Prove2me | Theorems.Thm_AnyPriceShare_Bidding_theorem_1_3
-- name    : AnyPriceShare.Bidding.theorem_1_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:14:21.440185+00:00
-- url     : https://prove2.me/theorems/1833127e-a030-4b6d-9933-d9334c7da49b
-- title:
--   Theorem 1.3, p. 5 — every additive instance has an allocation giving each agent max{3/5, 1/(2−b_i)} of her AnyPrice share
-- statement:
--   Consider $n$ agents with additive valuations $v_1,\dots,v_n$ over a set $M$ of $m$ indivisible items (non-negative item values $v_i(j)$, $v_i(T)=\sum_{j\in T}v_i(j)$) and entitlements $b_1,\dots,b_n$ with $b_i>0$ and $\sum_ib_i=1$. Then there is an allocation $(A_1,\dots,A_n)$ of all items in which every agent $i$ gets at least a $\max\{\frac35,\frac1{2-b_i}\}$ fraction of her AnyPrice share:
--
--   $$v_i(A_i)\ \ge\ \max\Big\{\frac35,\ \frac1{2-b_i}\Big\}\cdot\mathrm{AnyPrice}(b_i,v_i,M)\qquad\text{for every agent } i.$$
--
--   This is the main result of the paper: the first guarantee of a constant fraction of any share for agents with arbitrary entitlements. Since $\frac1{2-b_i}\to1$ as $b_i\to1$, agents with large entitlements get close to their full AnyPrice share.
--
--   **Formalization Note** An allocation is a map sending each item to an agent (a partition of all items into $n$ possibly empty bundles, as in §2). The AnyPrice share is the price form, Definition 1.1. The sentence "Moreover, such an allocation can be computed in polynomial time" is not formalized.
-- source:
--   Babaioff, Ezra & Feige, Fair-Share Allocations for Agents with Arbitrary Entitlements, arXiv:2103.04304v4, p. 5, Theorem 1.3

import Mathlib
import Definitions.Def_AnyPriceShare_Bidding_Basic

namespace AnyPriceShare.Bidding

/-- Theorem 1.3, p. 5, without its polynomial-time sentence: for every instance with `n` agents
with additive valuations `v` (non-negative item values) and entitlements `b` (`b i > 0`,
`∑ b i = 1`), there is an allocation of all items in which every agent `i` gets at least
`max {3/5, 1/(2 − b_i)}` times her AnyPrice share. -/
theorem theorem_1_3 {n m : ℕ} (v : Fin n → Fin m → ℝ) (hv : ∀ i j, 0 ≤ v i j)
    (b : Fin n → ℝ) (hb : ∀ i, 0 < b i) (hsum : ∑ i, b i = 1) :
    ∃ σ : Fin m → Fin n, ∀ i : Fin n,
      max (3 / 5) (1 / (2 - b i)) * anyPrice (b i) (addVal (v i)) Finset.univ
        ≤ addVal (v i) (allocBundle σ i) := by sorry

end AnyPriceShare.Bidding
