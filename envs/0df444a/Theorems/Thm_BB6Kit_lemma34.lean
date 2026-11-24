-- Prove2me | Theorems.Thm_BB6Kit_lemma34
-- name    : BB6Kit.lemma34
-- status  : Proved
-- author  : @alon yuval
-- created : 2026-11-24T07:21:05.298164+00:00
-- url     : https://prove2.me/theorems/7e7bbb41-73aa-4337-ac14-eeadb8cf5286
-- title:
--   Mignotte–Voutier Lemma 3.4: $KL(N-I)+\Theta(K-1,I)\ge\frac{N^2}{2K}(1+\frac2L-\frac6{KL}-\frac1{3L^2})$
-- statement:
--   **Lemma 3.4 of the Mignotte–Voutier kit.** Let $K\ge3$, $L\ge5$, $N=K(K+1)L/2$, and $0\le I\le N$. Then $$KL(N-I)+\Theta(K-1,I)\;\ge\;\frac{N^2}{2K}\Bigl(1+\frac2L-\frac6{KL}-\frac1{3L^2}\Bigr),$$ where $\Theta$ is the combinatorial minimum (3.1) (`BB6Theta.theta`).
--
--   The source proves it in two cases:
--
--   - $I\le N/2$: the term $KL(N-I)$ suffices.
--   - $I>N/2$: Lemma 3.3 gives $\Theta(K_0,I)\ge\tfrac{I^2}{2(K_0+1)}\bigl(1+\tfrac{(K_0-1)(K_0+1)}{I}-\tfrac{K_0(K_0+2)(K_0+1)^2}{12I^2}\bigr)$ for $I\ge K_0(K_0+1)/2$, with $K_0=K-1$.
--
--   Verified exactly, in rational arithmetic with exact $\Theta$, for all $3\le K\le15$, $5\le L\le29$ and $0\le I\le N$. The minimum slack is $16$, at $K=3$, $L=5$, $I=N$.
-- source:
--   Mignotte & Voutier (appendix by Laurent), A kit for linear forms in three logarithms, Math. Comp. (2023), arXiv:2205.08899, Lemma 3.4 (with Lemma 3.3).

import Mathlib
import Definitions.Def_BB6Theta

namespace BB6Kit
theorem lemma34 (K L N I : ℕ) (hK : 3 ≤ K) (hL : 5 ≤ L) (hN : N = K * (K + 1) * L / 2) (hI : I ≤ N) :
    (N : ℝ) ^ 2 / (2 * (K : ℝ)) * (1 + 2 / (L : ℝ) - 6 / ((K : ℝ) * L) - 1 / (3 * (L : ℝ) ^ 2)) ≤
      (K : ℝ) * L * ((N : ℝ) - I) + (BB6Theta.theta (K - 1) I : ℝ) := by
  sorry
end BB6Kit
