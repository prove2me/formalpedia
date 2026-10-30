-- Prove2me | Theorems.Thm_CubicTurning_unit_disk_law_double
-- name    : CubicTurning.unit_disk_law_double
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T19:58:56.512562+00:00
-- url     : https://prove2.me/theorems/b245fd54-f1c8-41ff-83e8-4c642b283714
-- title:
--   Doubling arbitrary unit-disk laws scales energy by four
-- statement:
--   For $e,d_0,d_1\in\mathbb C$, use Euclidean modulus $|z|=\sqrt{(\operatorname{Re}z)^2+(\operatorname{Im}z)^2}$ and set $h(e,d)=\operatorname{Im}(ed)/(|d|+\operatorname{Re}(ed))$, with real division by zero defined to be $0$. Let $T(e,d_0,d_1)$ mean $(h(e,d_0)\ge1/7\ \text{and}\ h(e,d_1)\le-1/7)$ or the same two inequalities with $d_0,d_1$ exchanged. Put $B(d_0,d_1)=2(|d_0||d_1|-\operatorname{Re}(d_0\overline{d_1}))$, $E(e,d_0,d_1)=B(d_0,d_1)$ if $T$ holds and $0$ otherwise, and $A(e,d_0,d_1)=(|d_0|+\operatorname{Re}(ed_0))(|d_1|+\operatorname{Re}(ed_1))(h(e,d_0)-h(e,d_1))^2$ if $T$ holds and $0$ otherwise. Every threshold inequality is non-strict. For complex $a,b,c$ put $P_{a,b,c}(X)=(X-a)(X-b)(X-c)$. A length-three chain $z=(z_0,z_1,z_2)$ means precisely $P_{a,b,c}^{\prime\prime}(z_0)=0$, $P_{a,b,c}^{\prime}(z_1)=0$, and $P_{a,b,c}(z_2)=0$. Being forward for an axis $e$ and consecutive displacements $d_0=z_1-z_0$, $d_1=z_2-z_1$ means $|e|=1$, $\operatorname{Re}(ed_0)\ge0$, and $\operatorname{Re}(ed_1)\ge0$; zero displacements and zero projections are allowed. A finite balanced forward law with $n$ slots for $a,b,c$ consists of real weights $w_i\ge0$ for $0\le i<n$ with $\sum_i w_i=1$, length-three chains $z^{(i)}$ for this same triple, and axes $e_i$ forward for those chains, with the complex equality $\sum_i(w_i:\mathbb C)z^{(i)}_2=0$. Its mean energy is $\mathcal E=\sum_iw_iE(e_i,z^{(i)}_1-z^{(i)}_0,z^{(i)}_2-z^{(i)}_1)$. A slot is not prescribed to terminate at a particular labelled root, weights may be zero, and all slots, including zero-weight slots, must satisfy their chain and forward conditions. No separate common-start field is required. For $n=0$ the normalization is impossible because the empty sum is $0$, so there is no such law. For real $t$, define $\widehat a_t=\mathrm i t/2$, $\widehat b_t=\frac12\sqrt{3+3t^2/4}-\mathrm i t/4$, and $\widehat c_t=-\frac12\sqrt{3+3t^2/4}-\mathrm i t/4$, using the nonnegative real square root. For real $t$, define $a_t=\mathrm i t$, $b_t=\sqrt{3+3t^2/4}-\mathrm i t/2$, and $c_t=-\sqrt{3+3t^2/4}-\mathrm i t/2$, with the nonnegative real square root. Put $V(a,b,c)=(|a|^2+|b|^2+|c|^2)/3$ and $q(t)=(2+2\sqrt{1+t^2})/3$. For every natural $n$, every real $t$, and every finite balanced forward law $L$ with $n$ slots for $(\widehat a_t,\widehat b_t,\widehat c_t)$, there exists a finite balanced forward law $M$ with the same number $n$ of slots for $(a_t,b_t,c_t)$ whose mean energy satisfies $\mathcal E_M=4\mathcal E_L$. There is no positivity or upper-bound hypothesis on $t$. The conclusion specifies existence and this energy equality; it does not require equal weights or axes or any particular relation between individual paths as part of the statement. At $n=0$ the premise law cannot exist.
-- source:
--   Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/continuation/CUBIC_TURNING.md (SHA-256 700f272e9074fa24f04f5fbdc8402cabc1521b4f114ad4cf29f05fc31e11b5b8), with signed-energy definitions in research-results/unified-20261025/proofs/SIGNED_TURNING.md (SHA-256 f092149c0133465022966bc4ecfc5f8227dd5219b0929ed5ac7bbef6d7a5c4c9). New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/cubic_turning/CubicUnitDiskSharpness.lean, lines 93-143, SHA-256 3486e16bcc09bab7538233bfe9db0c946150a8b63d7fd8e010d7b7e24a4c2a8b. The new Lean file is not present in the analytic source commit.

import Mathlib
import Definitions.Def_CubicTurning_finite_balanced
import Definitions.Def_CubicTurning_unit_disk
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
open ComplexConjugate

theorem CubicTurning.unit_disk_law_double {n : ℕ} (t : ℝ)
    (L : FiniteBalancedForwardLaw n (unitDiskCentral t) (unitDiskOuterPlus t) (unitDiskOuterMinus t)) :
    ∃ M : FiniteBalancedForwardLaw n (sharpCentral t) (sharpOuterPlus t) (sharpOuterMinus t),
      M.meanEnergy=4*L.meanEnergy := by sorry
