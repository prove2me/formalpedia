-- Prove2me | Theorems.Thm_BFAlmostLinear_subclaim_2_6
-- name    : BFAlmostLinear.subclaim_2_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:37:54.015188+00:00
-- url     : https://prove2.me/theorems/6f1cd140-afe3-4260-8264-7c5fc808362c
-- title:
--   Subclaim 2.6 — balanced partitions with $|\mathcal Y[S_i,r,T_j]|\le O(\log^2 n/\log\log n)$ (corrected: $\lceil n/\ell\rceil$ parts of size at most $\ell$)
-- statement:
--   There is $K>0$ with the following property. Let $V$ be a finite set with $n\ge3$ elements, $N\subseteq V$, $\ell$ an integer with $1\le\ell\le n$, and $\mathcal Y\subseteq V\times N\times V$ such that for all $r\in N$, $s,t\in V$:
--   1. $|\mathcal Y[*,r,*]|\le n^2/\ell^2$,
--   2. $|\mathcal Y[s,r,*]|\le n/\ell$,
--   3. $|\mathcal Y[*,r,t]|\le n/\ell$.
--
--   Then there are partitions $\{S_1,\dots,S_p\}$ and $\{T_1,\dots,T_p\}$ of $V$ into $p=\lceil n/\ell\rceil$ parts of size at most $\ell$ (some parts may be empty) such that for every $r\in N$ and $i,j\le p$,
--   $$|\mathcal Y[S_i,r,T_j]|\le K\,\frac{\log^2 n}{\log\log n}.$$
--
--   This partition lets Lemma 2.2 apply Lemma 2.4 block by block.
--
--   Differences from the source:
--   - correction: "partitions … each with $n/\ell$ subsets of size $\ell$" → $\lceil n/\ell\rceil$ subsets of size at most $\ell$; reason: at $n=3$, $\ell=2$ every assumption holds (take $\mathcal Y=\emptyset$) and $3$ vertices do not split into $2$-sets; if $\ell\mid n$, parts of size at most $\ell$ covering $V$ have size exactly $\ell$ up to empty parts.
--   - reading: real $\ell\ge1$ → integer $1\le\ell\le n$; reason: parts of size $\ell$ need an integer $\ell$, and for $\ell>n$ assumption 1 forces $\mathcal Y=\emptyset$.
--   - encoding: $n\ge3$; reason: $\log\log n\le0$ for $n\le2$, where the printed bound has no meaning.
--   - encoding: $O(\cdot)$ → a constant $K$; reason: Lean form of the $O$.
-- source:
--   Hair, Li, Li, Zhang, Bellman-Ford in Almost-Linear Time, STOC 2027 submission (manuscript sha256 873b9acb…), Subclaim 2.6, p.8, under assumptions 1–3 of Lemma 2.2, p.6

import Mathlib

namespace BFAlmostLinear

open Classical in
/-- **Subclaim 2.6**, p.8 (corrected: parts of size at most `ℓ`). "There exist partitions {S_1, …, S_{n/ℓ}} and
{T_1, …, T_{n/ℓ}} of V, each with n/ℓ subsets of size ℓ, such that |Y[S_i, r, T_j]| ≤ O(log² n / log log n) for each
r ∈ N and i, j ∈ [n/ℓ]." The hypotheses are assumptions 1–3 of Lemma 2.2, p.6.

Hair, Li, Li, Zhang, *Bellman-Ford in Almost-Linear Time*, STOC 2027 submission (manuscript sha256
873b9acb…), Subclaim 2.6, p.8.

**Formalization Note.**
* The printed partition does not exist for `ℓ ∤ n`: at `n = 3`, `ℓ = 2` every assumption holds, and 3 vertices do not
  split into 2-sets. The minimal correction is `⌈n/ℓ⌉` parts of size at most `ℓ`, for an integer `1 ≤ ℓ ≤ n`; if
  `ℓ ∣ n`, the parts have size exactly `ℓ`.
* `n ≥ 3` makes `log log n > 0`. The slices are filters of the finite set `Y`. -/
theorem subclaim_2_6 :
    ∃ K : ℝ, 0 < K ∧
      ∀ (V : Type) [Fintype V] (N : Finset V) (Y : Finset (V × V × V)) (ℓ : ℕ),
        3 ≤ Fintype.card V → 1 ≤ ℓ → ℓ ≤ Fintype.card V → (∀ x ∈ Y, x.2.1 ∈ N) →
        (∀ r ∈ N, (((Y.filter fun x => x.2.1 = r).card : ℕ) : ℝ) ≤
          (Fintype.card V : ℝ) ^ 2 / (ℓ : ℝ) ^ 2) →
        (∀ s, ∀ r ∈ N, (((Y.filter fun x => x.1 = s ∧ x.2.1 = r).card : ℕ) : ℝ) ≤
          (Fintype.card V : ℝ) / ℓ) →
        (∀ r ∈ N, ∀ t, (((Y.filter fun x => x.2.1 = r ∧ x.2.2 = t).card : ℕ) : ℝ) ≤
          (Fintype.card V : ℝ) / ℓ) →
        ∃ S T : Fin ⌈(Fintype.card V : ℝ) / ℓ⌉₊ → Finset V,
          (∀ i j, i ≠ j → Disjoint (S i) (S j)) ∧ (∀ v, ∃ i, v ∈ S i) ∧ (∀ i, (S i).card ≤ ℓ) ∧
          (∀ i j, i ≠ j → Disjoint (T i) (T j)) ∧ (∀ v, ∃ i, v ∈ T i) ∧ (∀ i, (T i).card ≤ ℓ) ∧
          ∀ r ∈ N, ∀ i j,
            (((Y.filter fun x => x.1 ∈ S i ∧ x.2.1 = r ∧ x.2.2 ∈ T j).card : ℕ) : ℝ) ≤
              K * Real.log (Fintype.card V) ^ 2 / Real.log (Real.log (Fintype.card V)) := by sorry

end BFAlmostLinear
