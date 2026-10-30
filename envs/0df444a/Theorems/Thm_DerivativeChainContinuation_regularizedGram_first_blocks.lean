-- Prove2me | Theorems.Thm_DerivativeChainContinuation_regularizedGram_first_blocks
-- name    : DerivativeChainContinuation.regularizedGram_first_blocks
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T20:22:17.02471+00:00
-- url     : https://prove2.me/theorems/236eddf2-6e5e-4aee-88a9-b2bbff575f5a
-- title:
--   Exact first-coordinate block form of a regularized Gram matrix
-- statement:
--   For a complex block matrix $T=\begin{pmatrix}a&r\\0&S\end{pmatrix}$ and arbitrary real $t$, the first-coordinate split gives $$G_t(T)=\begin{pmatrix}t+|a|^2&\overline a\,r\\a r^*&G_t(S)+r^*r\end{pmatrix}.$$ The formal statement includes the precise finite index equivalence.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/FirstGramBlock.lean#L18-L44

import Mathlib
import Definitions.Def_DerivativeChainContinuation_FirstGramBlock
import Definitions.Def_DerivativeChainContinuation_RegularizedGram
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Matrix
open scoped BigOperators

theorem DerivativeChainContinuation.regularizedGram_first_blocks (n : ℕ) (T : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (hcol : ∀ i : Fin n,T i.succ 0=0) (t : ℝ) :
    (regularizedGram T t).submatrix (firstSumEquiv n) (firstSumEquiv n) =
      fromBlocks
        (Matrix.of (fun _ _ : Unit => (t:ℂ)+(Complex.normSq (T 0 0):ℂ)))
        (Matrix.of (fun (_ : Unit) (j : Fin n) => star (T 0 0)*T 0 j.succ))
        (Matrix.of (fun (i : Fin n) (_ : Unit) => star (T 0 i.succ)*T 0 0))
        (regularizedGram (T.submatrix Fin.succ Fin.succ) t+
          vecMulVec (fun i => star (T 0 i.succ)) (fun j => T 0 j.succ)) := by sorry
