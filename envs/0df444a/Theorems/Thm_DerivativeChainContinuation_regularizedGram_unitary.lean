-- Prove2me | Theorems.Thm_DerivativeChainContinuation_regularizedGram_unitary
-- name    : DerivativeChainContinuation.regularizedGram_unitary
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T20:12:51.343647+00:00
-- url     : https://prove2.me/theorems/98485052-4bd1-4b8f-80e7-9a1a176e6561
-- title:
--   Regularized Gram matrices under unitary conjugation
-- statement:
--   For a complex square matrix $M$, a unitary $Q$ and any real $t$, $$G_t(Q^*MQ)=Q^*G_t(M)Q,\qquad G_t(M)=tI+M^*M.$$
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/GramUnitary.lean#L14-L28

import Mathlib
import Definitions.Def_DerivativeChainContinuation_RegularizedGram
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Matrix Polynomial
open scoped BigOperators

theorem DerivativeChainContinuation.regularizedGram_unitary {n : ℕ} (M Q : Matrix (Fin n) (Fin n) ℂ)
    (hQ : Q ∈ unitaryGroup (Fin n) ℂ) (t : ℝ) :
    regularizedGram (Q.conjTranspose*M*Q) t=Q.conjTranspose*regularizedGram M t*Q := by sorry
