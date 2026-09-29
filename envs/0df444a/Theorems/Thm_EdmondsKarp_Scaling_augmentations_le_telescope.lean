-- Prove2me | Theorems.Thm_EdmondsKarp_Scaling_augmentations_le_telescope
-- name    : EdmondsKarp.Scaling.augmentations_le_telescope
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T12:27:18.168213+00:00
-- url     : https://prove2.me/theorems/ccf6c51c-5a59-4995-82df-96f21b02cc19
-- title:
--   Proof of Theorem 9, eq. (6) — total augmentations $\le f_0^* - \sum_{p=1}^{l-1} f_p^*$
-- statement:
--   Let $a_1,\dots,a_m$, $b_1,\dots,b_n$ be positive integers with $\sum_i a_i = \sum_j b_j$ ($m, n \ge 1$), let $d_{ij} \ge 0$, and let $l$ satisfy $a_i < 2^l$ and $b_j < 2^l$ for all $i, j$. Write
--   $$f_p^* = \min\Big(\sum_i \lfloor a_i/2^p\rfloor, \sum_j \lfloor b_j/2^p\rfloor\Big)$$
--   for the maximum-flow value of Problem $p$. For every run of the scaling method with $l$ phases, making $K_p$ augmentations in Problem $p$,
--   $$\sum_{p=0}^{l-1} K_p \;\le\; f_{l-1}^* + \sum_{p=1}^{l-1}\big(f_{p-1}^* - 2f_p^*\big) \;=\; f_0^* - \sum_{p=1}^{l-1} f_p^*. \qquad (6)$$
--
--   This is the counting step of the proof of Theorem 9; the remainder of the proof is an estimate of the right-hand side.
--
--   **Formalization Note** The inequality is stated in $\mathbb{Z}$ with the right-hand form $f_0^* - \sum_{p=1}^{l-1} f_p^*$, where $f_0^* = \min(\sum a_i, \sum b_j)$.
-- source:
--   Edmonds, Karp, Theoretical Improvements in Algorithmic Efficiency for Network Flow Problems, J. ACM 19(2), 1972, p. 260, proof of Theorem 9, eq. (6)

import Mathlib
import Definitions.Def_EdmondsKarp_Scaling_Transport
import Definitions.Def_EdmondsKarp_Scaling_Augmentation
import Definitions.Def_EdmondsKarp_Scaling_Run

namespace EdmondsKarp.Scaling

/-- Proof of Theorem 9, eq. (6) (p. 260): writing `f_p^* = min(∑_i [a_i/2^p], ∑_j [b_j/2^p])` for the
maximum-flow value of Problem `p`, the total number of augmentations of a run of the scaling method
is at most `f_{l-1}^* + ∑_{p=1}^{l-1} (f_{p-1}^* - 2 f_p^*) = f_0^* - ∑_{p=1}^{l-1} f_p^*`. -/
theorem augmentations_le_telescope {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (a : Fin m → ℕ)
    (b : Fin n → ℕ) (d : Fin m → Fin n → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j)
    (hsum : ∑ i, a i = ∑ j, b j) (hd : ∀ i j, 0 ≤ d i j) (l : ℕ)
    (hla : ∀ i, a i < 2 ^ l) (hlb : ∀ j, b j < 2 ^ l) (K : ℕ → ℕ) (F : ℕ → ℕ → Flow m n)
    (hR : IsScalingRun a b d l K F) :
    ((∑ p ∈ Finset.range l, K p : ℕ) : ℤ) ≤
      ((min (∑ i, a i) (∑ j, b j) : ℕ) : ℤ) -
        ∑ p ∈ Finset.Ico 1 l, ((min (∑ i, a i / 2 ^ p) (∑ j, b j / 2 ^ p) : ℕ) : ℤ) := by sorry

end EdmondsKarp.Scaling
