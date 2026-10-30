-- Prove2me | Theorems.Thm_DerivativeChainContinuation_constant_unitary_compression
-- name    : DerivativeChainContinuation.constant_unitary_compression
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T19:46:35.192518+00:00
-- url     : https://prove2.me/theorems/df683f0d-28b4-4050-8030-3cb59c092575
-- title:
--   Compression in a basis with constant first column
-- statement:
--   For complex source slots $a_i$ in dimension $n+1$, let $B=P\operatorname{diag}(a)P$. If a unitary $Q$ has constant first column $1/\sqrt{n+1}$ and $E=\operatorname{diag}(0,1,\ldots,1)$, then $$Q^*BQ=E(Q^*\operatorname{diag}(a)Q)E.$$ No source-centering assumption is imposed.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/CompressionUnitary.lean#L35-L54

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CompressionGeometry
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem DerivativeChainContinuation.constant_unitary_compression (n : ℕ) (a : Fin (n+1) → ℂ)
    (Q : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (hQ : Q ∈ unitaryGroup (Fin (n+1)) ℂ)
    (hfirst : ∀ i, Q i 0=((Real.sqrt (n+1:ℝ))⁻¹:ℂ)) :
    Q.conjTranspose*rootCompression a*Q =
      diagonal (Fin.cases 0 (fun _ => 1)) * (Q.conjTranspose*diagonal a*Q) *
        diagonal (Fin.cases 0 (fun _ => 1)) := by sorry
