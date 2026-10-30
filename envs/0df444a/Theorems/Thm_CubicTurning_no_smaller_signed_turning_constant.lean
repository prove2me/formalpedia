-- Prove2me | Theorems.Thm_CubicTurning_no_smaller_signed_turning_constant
-- name    : CubicTurning.no_smaller_signed_turning_constant
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T19:51:54.641515+00:00
-- url     : https://prove2.me/theorems/a83dee64-48e8-443a-bf5d-9a836baa190f
-- title:
--   No smaller signed-turning constant works for finite laws
-- statement:
--   For $e,d_0,d_1\in\mathbb C$, use Euclidean modulus $|z|=\sqrt{(\operatorname{Re}z)^2+(\operatorname{Im}z)^2}$ and set $h(e,d)=\operatorname{Im}(ed)/(|d|+\operatorname{Re}(ed))$, with real division by zero defined to be $0$. Let $T(e,d_0,d_1)$ mean $(h(e,d_0)\ge1/7\ \text{and}\ h(e,d_1)\le-1/7)$ or the same two inequalities with $d_0,d_1$ exchanged. Put $B(d_0,d_1)=2(|d_0||d_1|-\operatorname{Re}(d_0\overline{d_1}))$, $E(e,d_0,d_1)=B(d_0,d_1)$ if $T$ holds and $0$ otherwise, and $A(e,d_0,d_1)=(|d_0|+\operatorname{Re}(ed_0))(|d_1|+\operatorname{Re}(ed_1))(h(e,d_0)-h(e,d_1))^2$ if $T$ holds and $0$ otherwise. Every threshold inequality is non-strict. For complex $a,b,c$ put $P_{a,b,c}(X)=(X-a)(X-b)(X-c)$. A length-three chain $z=(z_0,z_1,z_2)$ means precisely $P_{a,b,c}^{\prime\prime}(z_0)=0$, $P_{a,b,c}^{\prime}(z_1)=0$, and $P_{a,b,c}(z_2)=0$. Being forward for an axis $e$ and consecutive displacements $d_0=z_1-z_0$, $d_1=z_2-z_1$ means $|e|=1$, $\operatorname{Re}(ed_0)\ge0$, and $\operatorname{Re}(ed_1)\ge0$; zero displacements and zero projections are allowed. A finite balanced forward law with $n$ slots for $a,b,c$ consists of real weights $w_i\ge0$ for $0\le i<n$ with $\sum_i w_i=1$, length-three chains $z^{(i)}$ for this same triple, and axes $e_i$ forward for those chains, with the complex equality $\sum_i(w_i:\mathbb C)z^{(i)}_2=0$. Its mean energy is $\mathcal E=\sum_iw_iE(e_i,z^{(i)}_1-z^{(i)}_0,z^{(i)}_2-z^{(i)}_1)$. A slot is not prescribed to terminate at a particular labelled root, weights may be zero, and all slots, including zero-weight slots, must satisfy their chain and forward conditions. No separate common-start field is required. For $n=0$ the normalization is impossible because the empty sum is $0$, so there is no such law. For real $t$, define $a_t=\mathrm i t$, $b_t=\sqrt{3+3t^2/4}-\mathrm i t/2$, and $c_t=-\sqrt{3+3t^2/4}-\mathrm i t/2$, with the nonnegative real square root. Put $V(a,b,c)=(|a|^2+|b|^2+|c|^2)/3$ and $q(t)=(2+2\sqrt{1+t^2})/3$. For every real $K<2/3$, there exists a real $t$ with $0<t\le1$ such that for every natural $n$ and every finite balanced forward law for $(a_t,b_t,c_t)$ with $n$ slots, $K V(a_t,b_t,c_t)<\sum_{i=0}^{n-1}w_i A(e_i,z^{(i)}_1-z^{(i)}_0,z^{(i)}_2-z^{(i)}_1)$. The inequality is strict. The same $t$ works for all cardinalities and laws; no sign condition on $K$ is present, and $K=2/3$ is excluded. Zero weights are allowed, and the $n=0$ case is vacuous because no normalized law exists.
-- source:
--   Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/continuation/CUBIC_TURNING.md (SHA-256 700f272e9074fa24f04f5fbdc8402cabc1521b4f114ad4cf29f05fc31e11b5b8), with signed-energy definitions in research-results/unified-20261025/proofs/SIGNED_TURNING.md (SHA-256 f092149c0133465022966bc4ecfc5f8227dd5219b0929ed5ac7bbef6d7a5c4c9). New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/cubic_turning/CubicSharpness.lean, lines 352-362, SHA-256 387285b9af69f97f92225f56b89ed0b82ae043d24968cf05a356099163011707. The new Lean file is not present in the analytic source commit.

import Mathlib
import Definitions.Def_CubicTurning_finite_balanced
import Definitions.Def_CubicTurning_foundations
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
open ComplexConjugate

theorem CubicTurning.no_smaller_signed_turning_constant (K : ℝ) (hK : K<2/3) :
    ∃ t : ℝ, 0<t ∧ t≤1 ∧
      ∀ (n : ℕ) (L : FiniteBalancedForwardLaw n (sharpCentral t) (sharpOuterPlus t) (sharpOuterMinus t)),
        K*variance (sharpCentral t) (sharpOuterPlus t) (sharpOuterMinus t)<
          ∑ i,L.weights i*halfAngleEnergy (L.axes i)
            (L.paths i 1-L.paths i 0) (L.paths i 2-L.paths i 1) := by sorry
