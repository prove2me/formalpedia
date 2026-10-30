-- Prove2me | Theorems.Thm_CubicTurning_unit_disk_cubic_constant_sharp
-- name    : CubicTurning.unit_disk_cubic_constant_sharp
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T20:01:39.601193+00:00
-- url     : https://prove2.me/theorems/aa27cc7b-9c8c-4151-b802-0b75d2700bdb
-- title:
--   The two-thirds signed-turning constant is sharp inside the unit disk
-- statement:
--   For $e,d_0,d_1\in\mathbb C$, use Euclidean modulus $|z|=\sqrt{(\operatorname{Re}z)^2+(\operatorname{Im}z)^2}$ and set $h(e,d)=\operatorname{Im}(ed)/(|d|+\operatorname{Re}(ed))$, with real division by zero defined to be $0$. Let $T(e,d_0,d_1)$ mean $(h(e,d_0)\ge1/7\ \text{and}\ h(e,d_1)\le-1/7)$ or the same two inequalities with $d_0,d_1$ exchanged. Put $B(d_0,d_1)=2(|d_0||d_1|-\operatorname{Re}(d_0\overline{d_1}))$, $E(e,d_0,d_1)=B(d_0,d_1)$ if $T$ holds and $0$ otherwise, and $A(e,d_0,d_1)=(|d_0|+\operatorname{Re}(ed_0))(|d_1|+\operatorname{Re}(ed_1))(h(e,d_0)-h(e,d_1))^2$ if $T$ holds and $0$ otherwise. Every threshold inequality is non-strict. For complex $a,b,c$ put $P_{a,b,c}(X)=(X-a)(X-b)(X-c)$. A length-three chain $z=(z_0,z_1,z_2)$ means precisely $P_{a,b,c}^{\prime\prime}(z_0)=0$, $P_{a,b,c}^{\prime}(z_1)=0$, and $P_{a,b,c}(z_2)=0$. Being forward for an axis $e$ and consecutive displacements $d_0=z_1-z_0$, $d_1=z_2-z_1$ means $|e|=1$, $\operatorname{Re}(ed_0)\ge0$, and $\operatorname{Re}(ed_1)\ge0$; zero displacements and zero projections are allowed. A finite balanced forward law with $n$ slots for $a,b,c$ consists of real weights $w_i\ge0$ for $0\le i<n$ with $\sum_i w_i=1$, length-three chains $z^{(i)}$ for this same triple, and axes $e_i$ forward for those chains, with the complex equality $\sum_i(w_i:\mathbb C)z^{(i)}_2=0$. Its mean energy is $\mathcal E=\sum_iw_iE(e_i,z^{(i)}_1-z^{(i)}_0,z^{(i)}_2-z^{(i)}_1)$. A slot is not prescribed to terminate at a particular labelled root, weights may be zero, and all slots, including zero-weight slots, must satisfy their chain and forward conditions. No separate common-start field is required. For $n=0$ the normalization is impossible because the empty sum is $0$, so there is no such law. Write $V(a,b,c)=(|a|^2+|b|^2+|c|^2)/3$. For every real $K<2/3$, with no sign restriction on $K$, there exist a polynomial $p\in\mathbb C[X]$ and complex $a,b,c$ such that $p(X)=(X-a)(X-b)(X-c)$, $p$ is monic, its natural degree is exactly three, every complex zero $z$ of $p$ satisfies $|z|\le1$, and $a+b+c=0$. For this same triple, every natural $n$ and every finite balanced forward law with $n$ slots satisfies the strict inequality $K V(a,b,c)<\sum_{i=0}^{n-1}w_i A(e_i,z^{(i)}_1-z^{(i)}_0,z^{(i)}_2-z^{(i)}_1)$. The root-disk bound is non-strict, while the energy comparison is strict. The existential polynomial and roots may depend on $K$ and must work for all such finite laws and cardinalities; $n=0$ has no normalized law, and zero-weight slots are allowed for positive cardinalities. The statement imposes no distinct-root condition and no uniqueness of the existential witnesses; $K=2/3$ is excluded.
--
--   The witnesses are actual monic cubics whose complete root sets lie in the closed unit disk. Every finite balanced forward law for the chosen roots satisfies
--
--   $$K V<\sum_iw_i A(e_i,z^{(i)}_1-z^{(i)}_0,z^{(i)}_2-z^{(i)}_1),\qquad K<\frac23.$$
--
--   The strict comparison quantifies over all finite cardinalities and all admissible real weights; it is not restricted to the three constructed uniform histories.
-- source:
--   Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/continuation/CUBIC_TURNING.md (SHA-256 700f272e9074fa24f04f5fbdc8402cabc1521b4f114ad4cf29f05fc31e11b5b8), with signed-energy definitions in research-results/unified-20261025/proofs/SIGNED_TURNING.md (SHA-256 f092149c0133465022966bc4ecfc5f8227dd5219b0929ed5ac7bbef6d7a5c4c9). New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/cubic_turning/CubicUnitDiskSharpness.lean, lines 193-203, SHA-256 3486e16bcc09bab7538233bfe9db0c946150a8b63d7fd8e010d7b7e24a4c2a8b. The new Lean file is not present in the analytic source commit.

import Mathlib
import Definitions.Def_CubicTurning_finite_balanced
import Definitions.Def_CubicTurning_foundations
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
open ComplexConjugate

theorem CubicTurning.unit_disk_cubic_constant_sharp (K : ℝ) (hK : K<2/3) :
    ∃ (p : Polynomial ℂ) (a b c : ℂ),
      p=DerivativeChainPrivate.fromRoots (![a,b,c] : Fin 3 → ℂ) ∧
      p.Monic ∧ p.natDegree=3 ∧ (∀ z : ℂ,p.eval z=0 → ‖z‖≤1) ∧
      a+b+c=0 ∧
      ∀ (n : ℕ) (L : FiniteBalancedForwardLaw n a b c),
        K*variance a b c < ∑ i,L.weights i*halfAngleEnergy (L.axes i)
          (L.paths i 1-L.paths i 0) (L.paths i 2-L.paths i 1) := by sorry
