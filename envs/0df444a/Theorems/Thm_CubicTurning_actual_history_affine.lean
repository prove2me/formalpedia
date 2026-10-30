-- Prove2me | Theorems.Thm_CubicTurning_actual_history_affine
-- name    : CubicTurning.actual_history_affine
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T19:21:27.800295+00:00
-- url     : https://prove2.me/theorems/d9b6d7db-c92c-46cd-8d8f-526d66c75e12
-- title:
--   Affine images of explicit cubic derivative histories
-- statement:
--   For real $r$ and complex $v$, set $m_r(v)=r$ if $\operatorname{Re}v\ge0$, and $m_r(v)=-r$ otherwise, viewed as complex numbers. Set $f_r(v)=1$ if $r\le\operatorname{Re}v$; otherwise set it to $-1$ if $\operatorname{Re}v\le-r$; otherwise set it to $-\mathrm i$ if $\operatorname{Im}v\ge0$ and to $\mathrm i$ otherwise, with these cases tested in this order. For every real $r$ and complex $a,b,c,v,u,t$, if $a+b+c=0$, $a^2+b^2+c^2=6r^2$ as a complex equality, and $v=a$ or $v=b$ or $v=c$, then for $P(X)=(X-(u+ta))(X-(u+tb))(X-(u+tc))$, $P^{\prime\prime}(u)=0$, $P^{\prime}(u+tm_r(v))=0$, and $P(u+tv)=0$. No condition $r\ge0$, $|t|=1$, or $t\ne0$ is assumed; collapsed affine images and repeated values are included.
-- source:
--   Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/continuation/CUBIC_TURNING.md (SHA-256 700f272e9074fa24f04f5fbdc8402cabc1521b4f114ad4cf29f05fc31e11b5b8), with signed-energy definitions in research-results/unified-20261025/proofs/SIGNED_TURNING.md (SHA-256 f092149c0133465022966bc4ecfc5f8227dd5219b0929ed5ac7bbef6d7a5c4c9). New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/cubic_turning/CubicTurning.lean, lines 351-372, SHA-256 777a708fb09a3fa79468bea20924defade96d607f8974be374e179ef1fadc45b. The new Lean file is not present in the analytic source commit.

import Mathlib
import Definitions.Def_CubicTurning_foundations
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
open ComplexConjugate

theorem CubicTurning.actual_history_affine (r : ℝ) (a b c v u t : ℂ)
    (hcenter : a+b+c=0) (hsecond : a^2+b^2+c^2=6*(r:ℂ)^2)
    (hv : v=a ∨ v=b ∨ v=c) :
    DerivativeChainPrivate.IsChain ![u+t*a,u+t*b,u+t*c]
      ![u,u+t*middle r v,u+t*v] := by sorry
