-- Prove2me | Theorems.Thm_CubicTurning_every_monic_cubic_uniform_forward_law
-- name    : CubicTurning.every_monic_cubic_uniform_forward_law
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T19:42:45.814173+00:00
-- url     : https://prove2.me/theorems/bb69d86d-a435-4a23-b076-2cba9fcdaa44
-- title:
--   Every monic complex cubic admits a bounded actual forward law
-- statement:
--   For complex $e,d_0,d_1$, set $h(e,d)=\operatorname{Im}(ed)/(|d|+\operatorname{Re}(ed))$, using the total real division convention that division by zero is $0$. Let $T(e,d_0,d_1)$ mean $[h(e,d_0)\ge 1/7\text{ and }h(e,d_1)\le-1/7]$ or the same two inequalities with $d_0,d_1$ exchanged. Define $E(e,d_0,d_1)=2(|d_0||d_1|-\operatorname{Re}(d_0\overline{d_1}))$ when $T$ holds, and $E=0$ otherwise. All threshold inequalities are non-strict, and all complex moduli are Euclidean. For every polynomial $p\in\mathbb C[X]$ that is monic and has natural degree exactly $3$, there exist complex numbers $a,b,c$ such that $p(X)=(X-a)(X-b)(X-c)$. Put $u=(a+b+c)/3$, $V=(|a-u|^2+|b-u|^2+|c-u|^2)/3$, and $H=|((a-u)^2+(b-u)^2+(c-u)^2)/3|$. For a labelled triple $a,b,c\in\mathbb C$ and $u\in\mathbb C$, put $P(X)=(X-a)(X-b)(X-c)$. A law consists of three labelled paths $z^{(i)}=(z^{(i)}_0,z^{(i)}_1,z^{(i)}_2)\in\mathbb C^3$ and three complex axes $e_i$, indexed by $i=0,1,2$, with $P^{\prime\prime}(z^{(i)}_0)=0$, $P^{\prime}(z^{(i)}_1)=0$, $P(z^{(i)}_2)=0$, $z^{(0)}_2=a$, $z^{(1)}_2=b$, $z^{(2)}_2=c$, $z^{(i)}_0=u$, $|e_i|=1$, and $\operatorname{Re}(e_i(z^{(i)}_1-z^{(i)}_0))\ge0$, $\operatorname{Re}(e_i(z^{(i)}_2-z^{(i)}_1))\ge0$. Its mean energy is $\overline E=\frac13\sum_{i=0}^2E(e_i,z^{(i)}_1-z^{(i)}_0,z^{(i)}_2-z^{(i)}_1)$. This is finite labelled averaging with weights $1/3$; repeated endpoint values retain separate labels and may have identical paths. For these same $a,b,c$, there exists such a law with common start $u=(a+b+c)/3$ satisfying, additionally and explicitly, $p^{(3-(j+1))}(z^{(i)}_j)=0$ for every $i,j\in\{0,1,2\}$, where the derivative orders are respectively $2,1,0$, and satisfying $\overline E\le[H+\sqrt{H(2V-H)}]/3$ and $\overline E\le(2/3)V$. Both inequalities are non-strict. The root enumeration and law are existential and need not be unique; repeated roots, a triple root, zero variance, and zero displacements are included. The zero polynomial and lower-degree polynomials are excluded by the hypotheses. No assumption that roots are real, no squarefree condition, and no greedy requirement is made. The terminal distribution is the equal-weight distribution on the three root slots with multiplicity.
-- source:
--   Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/continuation/CUBIC_TURNING.md (SHA-256 700f272e9074fa24f04f5fbdc8402cabc1521b4f114ad4cf29f05fc31e11b5b8), with signed-energy definitions in research-results/unified-20261025/proofs/SIGNED_TURNING.md (SHA-256 f092149c0133465022966bc4ecfc5f8227dd5219b0929ed5ac7bbef6d7a5c4c9). New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/cubic_turning/CubicTurning.lean, lines 535-553, SHA-256 777a708fb09a3fa79468bea20924defade96d607f8974be374e179ef1fadc45b. The new Lean file is not present in the analytic source commit.

import Mathlib
import Definitions.Def_CubicTurning_foundations
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
open ComplexConjugate

theorem CubicTurning.every_monic_cubic_uniform_forward_law (p : Polynomial ℂ)
    (hp : p.Monic) (hd : p.natDegree=3) :
    ∃ a b c : ℂ, p=DerivativeChainPrivate.fromRoots (![a,b,c] : Fin 3 → ℂ) ∧
      ∃ L : AffineUniformForwardLaw a b c (centroid a b c),
        (∀ i j : Fin 3, ((Polynomial.derivative^[3-(j.val+1)]) p).eval (L.paths i j)=0) ∧
        L.meanEnergy ≤ (anisotropy a b c +
          Real.sqrt (anisotropy a b c*(2*centeredVariance a b c-anisotropy a b c)))/3 ∧
        L.meanEnergy ≤ (2/3)*centeredVariance a b c := by sorry
