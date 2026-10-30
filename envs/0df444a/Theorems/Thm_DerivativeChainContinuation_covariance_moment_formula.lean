-- Prove2me | Theorems.Thm_DerivativeChainContinuation_covariance_moment_formula
-- name    : DerivativeChainContinuation.covariance_moment_formula
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T18:55:58.363988+00:00
-- url     : https://prove2.me/theorems/a56b9d00-54e2-469a-967d-a63fdee477e8
-- title:
--   A planar covariance expressed by complex second moments
-- statement:
--   For a finite complex list $a$, let $V$ be its mean squared norm and $H$ its mean square as a complex number. Its second-moment matrix is $$\Sigma=\frac12\begin{pmatrix}V+\Re H&\Im H\\\Im H&V-\Re H\end{pmatrix}.$$ For centered input this is the covariance matrix; the formula also covers the empty list using totalized division.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/Covariance.lean#L21-L37

import Mathlib
import Definitions.Def_DerivativeChainContinuation_Covariance
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem DerivativeChainContinuation.covariance_moment_formula {n : ℕ} (a : Fin n → ℂ) :
    covariance a =
      !![(secondMoment a + (holomorphicMoment a).re)/2, (holomorphicMoment a).im/2;
         (holomorphicMoment a).im/2, (secondMoment a - (holomorphicMoment a).re)/2] := by sorry
