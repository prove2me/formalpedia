-- Prove2me | Theorems.Thm_BraneBrauer_Orthogonal_wick_sum_perm
-- name    : BraneBrauer.Orthogonal.wick_sum_perm
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T09:28:41.484001+00:00
-- url     : https://prove2.me/theorems/2234bbae-718e-4a61-9d37-da11b5ac3f1f
-- title:
--   Figure 3 — Wick pairings form a permutation sum
-- statement:
--   For $r$ entries of the first Gaussian matrix and $r$ conjugate entries, indexed by tuples $a,b,c,d\in\{1,\ldots,N\}^r$, Wick pairing gives
--   $$
--   \mathbb E\!\left[\overline{\prod_{k=1}^{r}(Z_A)_{a_k b_k}}\prod_{k=1}^{r}(Z_A)_{c_k d_k}\right]
--   =\sum_{\pi\in S_r}\prod_{k=1}^{r}
--   \delta_{a_k,c_{\pi(k)}}\delta_{b_k,d_{\pi(k)}}.
--   $$
--   Each permutation records which conjugate factor is paired with which ordinary factor. This is the entrywise form of the diagrammatic correlator of Figure 3.
--
--   **Formalization Note** The empty product at $r=0$ is one, and $S_0$ has one element; the formula includes that boundary case.
-- source:
--   Kimura & Ramgoolam, Branes, Anti-Branes and Brauer Algebras in Gauge-Gravity duality, arXiv:0709.2158v2, p. 7, text after (3.3) and Figure 3; p. 29, text before (7.13)

import Mathlib
import Definitions.Def_BraneBrauer_Orthogonal_Setting

noncomputable section
open scoped BigOperators

namespace BraneBrauer.Orthogonal

/-- Figure 3, p. 7: Wick pairings of `r` matrix entries are indexed
by permutations of the copies. -/
theorem wick_sum_perm {N r : ℕ}
    (a b c d : Fin r → Fin N) :
    (∫ Z, star (∏ k : Fin r, Z 0 (a k) (b k)) *
      (∏ k : Fin r, Z 0 (c k) (d k)) ∂matrixGaussian N) =
    ∑ π : Equiv.Perm (Fin r),
      ∏ k : Fin r,
        if a k = c (π k) ∧ b k = d (π k) then (1 : ℂ) else 0 := by sorry

end BraneBrauer.Orthogonal
