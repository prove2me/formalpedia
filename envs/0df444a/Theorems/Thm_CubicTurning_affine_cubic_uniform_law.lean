-- Prove2me | Theorems.Thm_CubicTurning_affine_cubic_uniform_law
-- name    : CubicTurning.affine_cubic_uniform_law
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T19:25:35.680669+00:00
-- url     : https://prove2.me/theorems/fa1b1311-c510-4e58-a3fa-3f66d37351fd
-- title:
--   Affine cubic law with anisotropic and variance bounds
-- statement:
--   For complex $e,d_0,d_1$, set $h(e,d)=\operatorname{Im}(ed)/(|d|+\operatorname{Re}(ed))$, using the total real division convention that division by zero is $0$. Let $T(e,d_0,d_1)$ mean $[h(e,d_0)\ge 1/7\text{ and }h(e,d_1)\le-1/7]$ or the same two inequalities with $d_0,d_1$ exchanged. Define $E(e,d_0,d_1)=2(|d_0||d_1|-\operatorname{Re}(d_0\overline{d_1}))$ when $T$ holds, and $E=0$ otherwise. All threshold inequalities are non-strict, and all complex moduli are Euclidean. For a labelled triple $a,b,c\in\mathbb C$ and $u\in\mathbb C$, put $P(X)=(X-a)(X-b)(X-c)$. A law consists of three labelled paths $z^{(i)}=(z^{(i)}_0,z^{(i)}_1,z^{(i)}_2)\in\mathbb C^3$ and three complex axes $e_i$, indexed by $i=0,1,2$, with $P^{\prime\prime}(z^{(i)}_0)=0$, $P^{\prime}(z^{(i)}_1)=0$, $P(z^{(i)}_2)=0$, $z^{(0)}_2=a$, $z^{(1)}_2=b$, $z^{(2)}_2=c$, $z^{(i)}_0=u$, $|e_i|=1$, and $\operatorname{Re}(e_i(z^{(i)}_1-z^{(i)}_0))\ge0$, $\operatorname{Re}(e_i(z^{(i)}_2-z^{(i)}_1))\ge0$. Its mean energy is $\overline E=\frac13\sum_{i=0}^2E(e_i,z^{(i)}_1-z^{(i)}_0,z^{(i)}_2-z^{(i)}_1)$. This is finite labelled averaging with weights $1/3$; repeated endpoint values retain separate labels and may have identical paths. For every real $r\ge0$ and complex $a,b,c,u,t$ satisfying $|t|=1$, $a+b+c=0$, and $a^2+b^2+c^2=6r^2$ as a complex equality, put $V_0=(|a|^2+|b|^2+|c|^2)/3$. There exists a law of the described kind for the endpoint triple $(u+ta,u+tb,u+tc)$ with common start $u$, satisfying both $\overline E\le[2r^2+\sqrt{(2r^2)(2V_0-2r^2)}]/3$ and $\overline E\le(2/3)V_0$. Both inequalities are non-strict. Repetitions and $r=0$ are allowed; the scale $t$ here has modulus one, while $u$ is unrestricted.
-- source:
--   Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/continuation/CUBIC_TURNING.md (SHA-256 700f272e9074fa24f04f5fbdc8402cabc1521b4f114ad4cf29f05fc31e11b5b8), with signed-energy definitions in research-results/unified-20261025/proofs/SIGNED_TURNING.md (SHA-256 f092149c0133465022966bc4ecfc5f8227dd5219b0929ed5ac7bbef6d7a5c4c9). New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/cubic_turning/CubicTurning.lean, lines 388-441, SHA-256 777a708fb09a3fa79468bea20924defade96d607f8974be374e179ef1fadc45b. The new Lean file is not present in the analytic source commit.

import Mathlib
import Definitions.Def_CubicTurning_foundations
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
open ComplexConjugate

theorem CubicTurning.affine_cubic_uniform_law (r : ℝ) (a b c u t : ℂ) (hr : 0 ≤ r)
    (ht : ‖t‖=1) (hcenter : a+b+c=0) (hsecond : a^2+b^2+c^2=6*(r:ℂ)^2) :
    ∃ L : AffineUniformForwardLaw (u+t*a) (u+t*b) (u+t*c) u,
      L.meanEnergy ≤ (2*r^2+Real.sqrt ((2*r^2)*(2*variance a b c-2*r^2)))/3 ∧
      L.meanEnergy ≤ (2/3)*variance a b c := by sorry
