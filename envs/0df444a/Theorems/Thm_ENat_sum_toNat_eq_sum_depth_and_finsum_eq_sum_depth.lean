-- Prove2me | Theorems.Thm_ENat_sum_toNat_eq_sum_depth_and_finsum_eq_sum_depth
-- name    : ENat.sum_toNat_eq_sum_depth_and_finsum_eq_sum_depth
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/87aeba73-80d5-510d-b0d5-28b0e324c576
-- title:
--   Regrouping a place sum and a prime finsum by depth
-- statement:
--   Let $P_l$ and $P_r$ be types and $E, r$ natural numbers. On the left-hand side, let $T_{\mathrm{tot}}$ be a finite subset of $P_l$, let $\mathrm{ordZ} : P_l \to \mathbb{Z}$, let $\mathrm{dep} : P_l \to \mathbb{N}$ satisfy $1 \le \mathrm{dep}(V)$ and $\mathrm{dep}(V) + 1 \le rE$ for every $V \in T_{\mathrm{tot}}$, and let $T : \mathbb{N} \to$ (finite subsets of $P_l$) be such that $V \in T(p)$ holds exactly when $V \in T_{\mathrm{tot}}$ and $\mathrm{dep}(V) = p$. On the right-hand side, let $\mathrm{horiz}$ be a predicate on $P_r$, let $\mathrm{rk}, \mathrm{depQ} : P_r \to \mathbb{N}$ and $\mathrm{lenU}, \mathrm{mult} : P_r \to \mathbb{N}\cup\{\infty\}$, and assume that for every $Q$ with $\mathrm{horiz}(Q)$ and $\mathrm{mult}(Q) \neq 0$ one has $1 \le \mathrm{depQ}(Q)$, $\mathrm{depQ}(Q) + 1 \le rE$, $r\,\mathrm{lenU}(Q) = \mathrm{depQ}(Q)\,\mathrm{rk}(Q)$ in $\mathbb{N}\cup\{\infty\}$, $1 \le \mathrm{rk}(Q)$ and $\mathrm{lenU}(Q) \neq \infty$; assume further that $\{Q : \mathrm{horiz}(Q) \wedge \mathrm{mult}(Q) \neq 0\}$ is finite. Then, in $\mathbb{N}\cup\{\infty\}$, both $\sum_{V \in T_{\mathrm{tot}}} (\mathrm{ordZ}\,V)^{+} = \sum_{p=1}^{rE-1} \sum_{V \in T(p)} (\mathrm{ordZ}\,V)^{+}$ (each order truncated to $\mathbb{N}$ by `Int.toNat` before summing) and $\sum^{f}_{Q\,:\,\mathrm{horiz}(Q)} \mathrm{rk}(Q)\,\mathrm{mult}(Q) = \sum_{p=1}^{rE-1} \sum^{f}_{Q\,:\,\mathrm{horiz}(Q),\ r\,\mathrm{lenU}(Q) = p\,\mathrm{rk}(Q)} \mathrm{rk}(Q)\,\mathrm{mult}(Q)$, the index range being the integer interval $[1, rE-1]$.
--
--   This is the purely combinatorial regrouping step by depth index: a finite sum over places and a possibly infinite `finsum` over "horizontal" primes are each decomposed as the sum over depth levels $p \in [1, rE-1]$, with the level of a prime read off from the relation $r\,\mathrm{lenU}(Q) = p\,\mathrm{rk}(Q)$ rather than from $\mathrm{depQ}$ directly. It feeds the totalling step [`ModularCurve.PlaceSpecialization.ProlongationTuple.sum_ord_eq_finsum_rank_mul_length_of_total_eq`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.sum_ord_eq_finsum_rank_mul_length_of_total_eq), where per-depth comparisons between places over a node and primes of the crossing model are assembled into an identity between totals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ENat_sum_toNat_eq_sum_depth_and_finsum_eq_sum_depth.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ENat.sum_toNat_eq_sum_depth_and_finsum_eq_sum_depth
    {Pl Pr : Type*} (E r : ℕ)
    (Ttot : Finset Pl) (ordZ : Pl → ℤ)
    (dep : Pl → ℕ) (hdep : ∀ V ∈ Ttot, 1 ≤ dep V ∧ dep V + 1 ≤ r * E)
    (T : ℕ → Finset Pl) (hT : ∀ p V, V ∈ T p ↔ V ∈ Ttot ∧ dep V = p)
    (horiz : Pr → Prop) (rk : Pr → ℕ) (lenU mult : Pr → ℕ∞) (depQ : Pr → ℕ)
    (hdepQ : ∀ Q, horiz Q → mult Q ≠ 0 →
      1 ≤ depQ Q ∧ depQ Q + 1 ≤ r * E ∧ (r : ℕ∞) * lenU Q = ((depQ Q * rk Q : ℕ) : ℕ∞) ∧
        1 ≤ rk Q ∧ lenU Q ≠ ⊤)
    (hfin : {Q : Pr | horiz Q ∧ mult Q ≠ 0}.Finite) :
    ((∑ V ∈ Ttot, (ordZ V).toNat : ℕ) : ℕ∞) =
        ∑ p ∈ Finset.Icc 1 (r * E - 1), ((∑ V ∈ T p, (ordZ V).toNat : ℕ) : ℕ∞) ∧
    (∑ᶠ (Q : Pr) (_ : horiz Q), (rk Q : ℕ∞) * mult Q) =
        ∑ p ∈ Finset.Icc 1 (r * E - 1),
          ∑ᶠ (Q : Pr) (_ : horiz Q ∧ (r : ℕ∞) * lenU Q = ((p * rk Q : ℕ) : ℕ∞)), (rk Q : ℕ∞) * mult Q := by sorry
