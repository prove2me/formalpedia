-- Prove2me | Theorems.Thm_CubicTurning_uniform_energy_bound
-- name    : CubicTurning.uniform_energy_bound
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T19:23:24.793631+00:00
-- url     : https://prove2.me/theorems/48942a49-59f4-40cc-aff6-a994c78d0c38
-- title:
--   Uniform cubic energy from the transverse budget
-- statement:
--   For complex $e,d_0,d_1$, set $h(e,d)=\operatorname{Im}(ed)/(|d|+\operatorname{Re}(ed))$, using the total real division convention that division by zero is $0$. Let $T(e,d_0,d_1)$ mean $[h(e,d_0)\ge 1/7\text{ and }h(e,d_1)\le-1/7]$ or the same two inequalities with $d_0,d_1$ exchanged. Define $E(e,d_0,d_1)=2(|d_0||d_1|-\operatorname{Re}(d_0\overline{d_1}))$ when $T$ holds, and $E=0$ otherwise. All threshold inequalities are non-strict, and all complex moduli are Euclidean. For real $r$ and complex $v$, set $m_r(v)=r$ if $\operatorname{Re}v\ge0$, and $m_r(v)=-r$ otherwise, viewed as complex numbers. Set $f_r(v)=1$ if $r\le\operatorname{Re}v$; otherwise set it to $-1$ if $\operatorname{Re}v\le-r$; otherwise set it to $-\mathrm i$ if $\operatorname{Im}v\ge0$ and to $\mathrm i$ otherwise, with these cases tested in this order. For every real $r\ge0$ and complex $a,b,c$ satisfying $a+b+c=0$ and the complex equality $a^2+b^2+c^2=6r^2$, put $Y=(2/3)((\operatorname{Im}a)^2+(\operatorname{Im}b)^2+(\operatorname{Im}c)^2)$. Then $[E(f_r(a),m_r(a),a-m_r(a))+E(f_r(b),m_r(b),b-m_r(b))+E(f_r(c),m_r(c),c-m_r(c))]/3\le2r(\sqrt{r^2+Y}+r)/3$. The square equality constrains both real and imaginary parts; $r=0$ and repeated values are included, and the comparison is non-strict.
-- source:
--   Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/continuation/CUBIC_TURNING.md (SHA-256 700f272e9074fa24f04f5fbdc8402cabc1521b4f114ad4cf29f05fc31e11b5b8), with signed-energy definitions in research-results/unified-20261025/proofs/SIGNED_TURNING.md (SHA-256 f092149c0133465022966bc4ecfc5f8227dd5219b0929ed5ac7bbef6d7a5c4c9). New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/cubic_turning/CubicTurning.lean, lines 139-192, SHA-256 777a708fb09a3fa79468bea20924defade96d607f8974be374e179ef1fadc45b. The new Lean file is not present in the analytic source commit.

import Mathlib
import Definitions.Def_CubicTurning_foundations
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
open ComplexConjugate

theorem CubicTurning.uniform_energy_bound (r : ℝ) (a b c : ℂ) (hr : 0 ≤ r)
    (hcenter : a+b+c=0)
    (hsecond : a^2+b^2+c^2=6*(r:ℂ)^2) :
    let Y := (2/3)*(a.im^2+b.im^2+c.im^2)
    (endpointEnergy r a+endpointEnergy r b+endpointEnergy r c)/3 ≤
      (2*r*(Real.sqrt (r^2+Y)+r))/3 := by sorry
