-- Prove2me | Theorems.Thm_DetANN_HPIM_median_threshold
-- name    : DetANN.HPIM.median_threshold
-- status  : Proved
-- author  : @milia
-- created : 2026-11-16T05:52:26.125397+00:00
-- url     : https://prove2.me/theorems/5c124b11-3890-4624-b5e8-bf153f805377
-- title:
--   The threshold graph and its median threshold
-- statement:
--   Let $P_1,\dots,P_n\in\mathbb R^m$ (definition `DetANN_HPIMThreshold`).
--
--   1. If $d\ge0$, two points in the same component of the threshold graph at $d$ are within $(n-1)d$.
--   2. Every component has a representative.
--   3. If some component at $d$ has at least $\lfloor n/2\rfloor+1$ points, there are at most $\lceil n/2\rceil$ representatives at $d$.
--   4. If $n\ge2$ and the points are distinct, let $d^\ast$ be the median threshold. Then some component at $d^\ast$ has at least $\lfloor n/2\rfloor+1$ points, $d^\ast>0$, and for every $d<d^\ast$ every component at $d$ has at most $\lfloor n/2\rfloor$ points.
--
--   These are the facts about $r_{\mathrm{med}}=d^\ast/2$ that the tree of Har-Peled, Indyk and Motwani (2012, §2) uses. Recursing into a component at the lower threshold, or into the representatives at $d^\ast$, at least halves the point set, so the tree has depth $O(\log n)$. Item 1 bounds the diameters, and with them the length of the ladder of radii.
-- source:
--   Original, written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions' as part of a floor-free proof of DetANN.lemma_3_3 (Feng, Indyk, STOC 2027 submission, Lemma 3.3, p.7). The search tree follows Har-Peled, Indyk, Motwani, Approximate nearest neighbor: towards removing the curse of dimensionality, Theory of Computing 8 (2012), §2, made deterministic and floor-free.

import Mathlib
import Definitions.Def_DetANN_HPIMThreshold

namespace DetANN.HPIM

open Classical in
/-- **The threshold graph and its median threshold.** For points `P_1, …, P_n ∈ ℝ^m` and `d ∈ ℝ`:
1. points in the same component of the threshold graph at `d ≥ 0` are within `(n − 1) d`;
2. every component has a representative (its least index);
3. if some component has at least `⌊n/2⌋ + 1` points, there are at most `⌈n/2⌉` representatives;
4. if `n ≥ 2` and the points are distinct, then at `d = medThreshold P` some component has at least
   `⌊n/2⌋ + 1` points, `medThreshold P > 0`, and at every `d < medThreshold P` every component has at
   most `⌊n/2⌋` points. -/
theorem median_threshold {m n : ℕ} (P : Fin n → EuclideanSpace ℝ (Fin m)) :
    (∀ d : ℝ, 0 ≤ d → ∀ i j, thrReach P d i j → dist (P i) (P j) ≤ ((n : ℝ) - 1) * d) ∧
    (∀ (d : ℝ) (i : Fin n), ∃ j, thrReach P d i j ∧ IsRep P d j) ∧
    (∀ (d : ℝ) (i₀ : Fin n), n / 2 + 1 ≤ (Finset.univ.filter (thrReach P d i₀)).card →
      (Finset.univ.filter (IsRep P d)).card ≤ (n + 1) / 2) ∧
    (2 ≤ n → Function.Injective P →
      (∃ i, n / 2 + 1 ≤ (Finset.univ.filter (thrReach P (medThreshold P) i)).card) ∧
      0 < medThreshold P ∧
      ∀ d < medThreshold P, ∀ i, (Finset.univ.filter (thrReach P d i)).card ≤ n / 2) := by sorry

end DetANN.HPIM
