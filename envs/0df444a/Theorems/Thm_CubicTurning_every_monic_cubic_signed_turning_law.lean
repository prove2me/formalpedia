-- Prove2me | Theorems.Thm_CubicTurning_every_monic_cubic_signed_turning_law
-- name    : CubicTurning.every_monic_cubic_signed_turning_law
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T19:44:43.933722+00:00
-- url     : https://prove2.me/theorems/e4b7605f-7934-4686-b9e2-fe81399f21a6
-- title:
--   Every monic cubic has a balanced signed-turning law
-- statement:
--   For $e,d_0,d_1\in\mathbb C$, use Euclidean modulus $|z|=\sqrt{(\operatorname{Re}z)^2+(\operatorname{Im}z)^2}$ and set $h(e,d)=\operatorname{Im}(ed)/(|d|+\operatorname{Re}(ed))$, with real division by zero defined to be $0$. Let $T(e,d_0,d_1)$ mean $(h(e,d_0)\ge1/7\ \text{and}\ h(e,d_1)\le-1/7)$ or the same two inequalities with $d_0,d_1$ exchanged. Put $B(d_0,d_1)=2(|d_0||d_1|-\operatorname{Re}(d_0\overline{d_1}))$, $E(e,d_0,d_1)=B(d_0,d_1)$ if $T$ holds and $0$ otherwise, and $A(e,d_0,d_1)=(|d_0|+\operatorname{Re}(ed_0))(|d_1|+\operatorname{Re}(ed_1))(h(e,d_0)-h(e,d_1))^2$ if $T$ holds and $0$ otherwise. Every threshold inequality is non-strict. For complex $a,b,c$, put $u=(a+b+c)/3$, $V_c=(|a-u|^2+|b-u|^2+|c-u|^2)/3$, and $H=|((a-u)^2+(b-u)^2+(c-u)^2)/3|$. For complex $a,b,c$ put $P_{a,b,c}(X)=(X-a)(X-b)(X-c)$. A length-three chain $z=(z_0,z_1,z_2)$ means precisely $P_{a,b,c}^{\prime\prime}(z_0)=0$, $P_{a,b,c}^{\prime}(z_1)=0$, and $P_{a,b,c}(z_2)=0$. Being forward for an axis $e$ and consecutive displacements $d_0=z_1-z_0$, $d_1=z_2-z_1$ means $|e|=1$, $\operatorname{Re}(ed_0)\ge0$, and $\operatorname{Re}(ed_1)\ge0$; zero displacements and zero projections are allowed. A uniform labelled law for $a,b,c$ with start $u$ consists of three chains $z^{(i)}$, $i=0,1,2$, and axes $e_i$, each forward for its chain, satisfying $z^{(i)}_0=u$ and $z^{(0)}_2=a$, $z^{(1)}_2=b$, $z^{(2)}_2=c$. Its mean energy is $\overline E=\frac13\sum_{i=0}^{2}E(e_i,z^{(i)}_1-z^{(i)}_0,z^{(i)}_2-z^{(i)}_1)$. These are three equally weighted slots; repetitions remain separate slots, and no distinctness, independence, or greedy minimization condition is imposed. For every polynomial $p\in\mathbb C[X]$ that is monic and has natural degree exactly $3$, there exist complex $a,b,c$ with $p(X)=(X-a)(X-b)(X-c)$ and a uniform labelled law for this triple with start $u=(a+b+c)/3$ such that: for every $i,j\in\{0,1,2\}$, $p^{(3-(j+1))}(z^{(i)}_j)=0$, so the orders at $j=0,1,2$ are $2,1,0$; for every function $f:\mathbb C\to\mathbb R$, $\frac13\sum_i f(z^{(i)}_2)=(f(a)+f(b)+f(c))/3$; $\sum_i(1/3:\mathbb C)(z^{(i)}_2-u)=0$; and the scalar $\frac13\sum_iA(e_i,z^{(i)}_1-z^{(i)}_0,z^{(i)}_2-z^{(i)}_1)$ is at most both $(H+\sqrt{H(2V_c-H)})/3$ and $(2/3)V_c$. The same existential triple and law satisfy every conclusion. The two bounds are non-strict; $f$ has no regularity assumption. Repeated roots, a triple root, zero variance, and zero displacements are included; degree exactly three excludes lower-degree and zero polynomials. No uniqueness or greedy condition is asserted.
--
--   This is the all-monic-cubic upper result for a finite labelled law. For its single constructed law,
--
--   $$\overline A\le\frac{H+\sqrt{H(2V_c-H)}}3,\qquad \overline A\le\frac23V_c.$$
--
--   The terminal marginal counts root multiplicity; the statement includes every degenerate cubic allowed by monicity and degree three.
-- source:
--   Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/continuation/CUBIC_TURNING.md (SHA-256 700f272e9074fa24f04f5fbdc8402cabc1521b4f114ad4cf29f05fc31e11b5b8), with signed-energy definitions in research-results/unified-20261025/proofs/SIGNED_TURNING.md (SHA-256 f092149c0133465022966bc4ecfc5f8227dd5219b0929ed5ac7bbef6d7a5c4c9). New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/cubic_turning/CubicSignedTurning.lean, lines 20-34, SHA-256 d2a0c7c0d7b829f4c7da971457e333f60323f43736b0b1f6698063c908bd49f9. The new Lean file is not present in the analytic source commit.

import Mathlib
import Definitions.Def_CubicTurning_foundations
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
open ComplexConjugate

theorem CubicTurning.every_monic_cubic_signed_turning_law (p : Polynomial ℂ)
    (hp : p.Monic) (hd : p.natDegree=3) :
    ∃ a b c : ℂ, p=DerivativeChainPrivate.fromRoots (![a,b,c] : Fin 3 → ℂ) ∧
      ∃ L : AffineUniformForwardLaw a b c (centroid a b c),
        (∀ i j : Fin 3, ((Polynomial.derivative^[3-(j.val+1)]) p).eval (L.paths i j)=0) ∧
        (∀ f : ℂ → ℝ, (∑ i,f (L.paths i 2))/3=(f a+f b+f c)/3) ∧
        (∑ i,(1/3:ℂ)*(L.paths i 2-centroid a b c))=0 ∧
        (∑ i,halfAngleEnergy (L.axes i) (L.paths i 1-L.paths i 0) (L.paths i 2-L.paths i 1))/3 ≤
          (anisotropy a b c+Real.sqrt (anisotropy a b c*(2*centeredVariance a b c-anisotropy a b c)))/3 ∧
        (∑ i,halfAngleEnergy (L.axes i) (L.paths i 1-L.paths i 0) (L.paths i 2-L.paths i 1))/3 ≤
          (2/3)*centeredVariance a b c := by sorry
