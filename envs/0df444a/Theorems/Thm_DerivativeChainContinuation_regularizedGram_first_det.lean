-- Prove2me | Theorems.Thm_DerivativeChainContinuation_regularizedGram_first_det
-- name    : DerivativeChainContinuation.regularizedGram_first_det
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T20:24:32.31776+00:00
-- url     : https://prove2.me/theorems/78dcca9c-ae26-4153-8ee5-f73da610e695
-- title:
--   First-coordinate Schur determinant identity for a regularized Gram matrix
-- statement:
--   For $T=\begin{pmatrix}a&r\\0&S\end{pmatrix}$ and $t>0$, $$\det G_t(T)=(t+|a|^2)\det\left(G_t(S)+\frac{t}{t+|a|^2}r^*r\right).$$ The positive scalar denominator is explicit.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/GramSchurStep.lean#L8-L54

import Mathlib
import Definitions.Def_DerivativeChainContinuation_RegularizedGram
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Matrix
open scoped BigOperators

theorem DerivativeChainContinuation.regularizedGram_first_det (n : ℕ) (T : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (hcol : ∀ i : Fin n,T i.succ 0=0) (t : ℝ) (ht : 0 < t) :
    (regularizedGram T t).det =
      ((t+Complex.normSq (T 0 0):ℝ):ℂ)*
        (regularizedGram (T.submatrix Fin.succ Fin.succ) t+
          ((t/(t+Complex.normSq (T 0 0)):ℝ):ℂ) •
            vecMulVec (fun i : Fin n => star (T 0 i.succ)) (fun j : Fin n => T 0 j.succ)).det := by sorry
