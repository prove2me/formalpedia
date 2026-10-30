-- Prove2me | Theorems.Thm_DerivativeChainContinuation_pinned_schur_derivative_factorization
-- name    : DerivativeChainContinuation.pinned_schur_derivative_factorization
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T19:52:33.667908+00:00
-- url     : https://prove2.me/theorems/dd5589dd-695c-4e47-91ce-a64f63ef96e4
-- title:
--   The pinned Schur diagonal lists the actual derivative roots
-- statement:
--   Let $p(X)=\prod_{i=0}^{n}(X-a_i)$. In a unitary basis with constant first vector that triangularizes the root compression, let $b_j=(Q^*\operatorname{diag}(a)Q)_{j+1,j+1}$. Then $$\operatorname{monicDerivative}(p)=\prod_{j=0}^{n-1}(X-b_j).$$ Multiplicities are retained, including the empty product for $n=0$.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/PinnedSchur.lean#L40-L65

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CompressionGeometry
import Definitions.Def_DerivativeChainContinuation_PolynomialMoments
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem DerivativeChainContinuation.pinned_schur_derivative_factorization (n : ℕ) (a : Fin (n+1) → ℂ)
    (Q : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (hQ : Q ∈ unitaryGroup (Fin (n+1)) ℂ)
    (hfirst : ∀ i, Q i 0=((Real.sqrt (n+1:ℝ))⁻¹:ℂ))
    (ht : (Q.conjTranspose*rootCompression a*Q).IsUpperTriangular) :
    monicDerivative (∏ i, (X-C (a i))) =
      ∏ j : Fin n, (X-C ((Q.conjTranspose*diagonal a*Q) j.succ j.succ)) := by sorry
