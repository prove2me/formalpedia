-- Prove2me | Theorems.Thm_CubicTurning_sharp_family_polynomial
-- name    : CubicTurning.sharp_family_polynomial
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T19:54:09.555055+00:00
-- url     : https://prove2.me/theorems/947a6f34-e6e7-4b73-9e70-18e942156802
-- title:
--   Polynomial identity for the sharp cubic family
-- statement:
--   For real $t$, define $a_t=\mathrm i t$, $b_t=\sqrt{3+3t^2/4}-\mathrm i t/2$, and $c_t=-\sqrt{3+3t^2/4}-\mathrm i t/2$, with the nonnegative real square root. Put $V(a,b,c)=(|a|^2+|b|^2+|c|^2)/3$ and $q(t)=(2+2\sqrt{1+t^2})/3$. For every real $t$, the complex polynomial $(X-a_t)(X-b_t)(X-c_t)$ equals $X^3-3X+\mathrm i t(3+t^2)$. No positivity, upper bound, or nonzero hypothesis on $t$ is required; the identity includes $t=0$.
--
--   This identifies the actual polynomial behind the finite-law sharpness examples:
--
--   $$p_t(X)=X^3-3X+\mathrm i\,t(3+t^2)\qquad(t\in\mathbb R).$$
-- source:
--   Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/continuation/CUBIC_TURNING.md (SHA-256 700f272e9074fa24f04f5fbdc8402cabc1521b4f114ad4cf29f05fc31e11b5b8), with signed-energy definitions in research-results/unified-20261025/proofs/SIGNED_TURNING.md (SHA-256 f092149c0133465022966bc4ecfc5f8227dd5219b0929ed5ac7bbef6d7a5c4c9). New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/cubic_turning/CubicSharpness.lean, lines 364-393, SHA-256 387285b9af69f97f92225f56b89ed0b82ae043d24968cf05a356099163011707. The new Lean file is not present in the analytic source commit.

import Mathlib
import Definitions.Def_CubicTurning_finite_balanced
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
open ComplexConjugate

theorem CubicTurning.sharp_family_polynomial (t : ℝ) :
    DerivativeChainPrivate.fromRoots (![sharpCentral t,sharpOuterPlus t,sharpOuterMinus t] : Fin 3 → ℂ)=
      Polynomial.X^3-Polynomial.C 3*Polynomial.X+
        Polynomial.C (Complex.I*(t:ℂ)*(3+(t:ℂ)^2)) := by sorry
