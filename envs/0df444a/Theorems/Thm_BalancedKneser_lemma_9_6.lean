-- Prove2me | Theorems.Thm_BalancedKneser_lemma_9_6
-- name    : BalancedKneser.lemma_9_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:47:09.743434+00:00
-- url     : https://prove2.me/theorems/ab82c86d-b5af-494e-a2cd-f63712e3422e
-- title:
--   Lemma 9.6 (Radius-one rounding) — at most five $k$-sets with a fractional radius-one center have an integral one
-- statement:
--   Let $1\le k<N$. For a family $\sigma$ of $k$-subsets of $[N]$:
--
--   1. if $|\sigma|\le5$ and $\sigma$ has a common **fractional radius-one center**, i.e. a point $x\in[0,1]^N$ with $\sum_i x_i=k$ and $x(A)=\sum_{i\in A}x_i\ge k-1$ for every $A\in\sigma$, then $\sigma$ has a common **integral center**: a $k$-set $Z$ with Johnson distance $d_J(A,Z)=k-|A\cap Z|\le1$ for every $A\in\sigma$;
--   2. consequently $C_1(N,k)$ and $Y_1$ have the same four-skeleton: their faces with at most five vertices coincide.
--
--   At radius one this identifies the chain groups and boundary maps of $C_1(N,k)$ and $Y_1$ through degree four, which is all the comparison the six-color theorem needs.
--
--   Differences from the source:
--   - encoding: d_J(A, Z) ≤ 1 and the four-skeleton → k ≤ |A ∩ Z| + 1, and {σ ∈ C_1 | |σ| ≤ 5} = {σ ∈ Y_1 | |σ| ≤ 5}; reason: the four-skeleton consists of the faces of dimension at most four, i.e. with at most five vertices; same statement
-- source:
--   Alipour, Jafari, Balanced Fair Division and Generalized Kneser Graphs, arXiv:2611.04486v1, Lemma 9.6, p.21 (PDF p.23); standing hypothesis 1 ≤ k < N, §9.3, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_BalancedKneser_CC
import Definitions.Def_BalancedKneser_Yfrac

namespace BalancedKneser

/-- **Lemma 9.6 (Radius-one rounding)** (Alipour–Jafari, arXiv:2611.04486v1, p.21
(PDF p.23)): "At most five k-sets with a common fractional radius-one center have a common
integral center. Thus C1(N, k) and Y1 have the same four-skeleton."

Standing hypothesis of §9.3–9.6 (p.18): `1 ≤ k < N`. A fractional radius-one center of a family
`σ` of `k`-subsets of `[N]` is `x ∈ [0,1]^N` with `Σᵢ xᵢ = k` and `x(A) ≥ k − 1` for `A ∈ σ`;
an integral center is a `k`-set `Z` with Johnson distance `d_J(A, Z) = k − |A ∩ Z| ≤ 1` for
`A ∈ σ`. The four-skeleton of a complex consists of its faces with at most five vertices. -/
theorem lemma_9_6 (N k : ℕ) (hk : 1 ≤ k) (hkN : k < N) :
    (∀ σ : Finset (KSet N k), σ.card ≤ 5 →
      (∃ x : Fin N → ℝ, (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧ ∑ i, x i = k ∧
        ∀ A ∈ σ, (k : ℝ) - 1 ≤ ∑ i ∈ A.1, x i) →
      ∃ Z : Finset (Fin N), Z.card = k ∧ ∀ A ∈ σ, k ≤ (A.1 ∩ Z).card + 1) ∧
    {σ | σ ∈ CC 1 N k ∧ σ.card ≤ 5} = {σ | σ ∈ Yfrac 1 N k ∧ σ.card ≤ 5} := by sorry

end BalancedKneser
