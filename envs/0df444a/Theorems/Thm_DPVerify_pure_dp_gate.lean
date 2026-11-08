-- Prove2me | Theorems.Thm_DPVerify_pure_dp_gate
-- name    : DPVerify.pure_dp_gate
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:53:30.350029+00:00
-- url     : https://prove2.me/theorems/c1a15649-9397-44cb-a5d2-7702048ce30b
-- title:
--   Proof of Theorem 4.1, p.15 — pure DP: $b_S$ and $G$ are $2\varepsilon$-DP, their AND is $4\varepsilon$-DP
-- statement:
--   Let $\varepsilon\ge0$, $\kappa>0$ and $u>0$. Let $0\le q\le p$, and let $q',p'$ satisfy
--
--   $$
--   e^{-\varepsilon}q\le q'\le e^{\varepsilon}q,\qquad e^{-\varepsilon}(p-q)\le p'-q'\le e^{\varepsilon}(p-q)
--   $$
--
--   (on two neighbouring samples, $q=q_S(m,a)$ and $p-q$ are the joint probabilities of sending $m$ and accepting, respectively rejecting, the reply $a$; then $p'$ is within a factor $e^\varepsilon$ of $p$ as well). Let $b=q/p$ (with $b=0$ when $p=0$) and $G=G(p,u)$. Then:
--
--   1. $b'\le e^{2\varepsilon}b$ and $1-b'\le e^{2\varepsilon}(1-b)$;
--   2. $G(p',u)\le e^{2\varepsilon}G(p,u)$ and $1-G(p',u)\le e^{2\varepsilon}(1-G(p,u))$;
--   3. for every real $y$: $\dfrac{e^{2\varepsilon}}{y^2+e^{2\varepsilon}}\le e^{2\varepsilon}\dfrac1{y^2+1}$ and $\dfrac{e^{-2\varepsilon}}{y^2+e^{-2\varepsilon}}\ge e^{-2\varepsilon}\dfrac1{y^2+1}$;
--   4. $G(p',u)\,b'\le e^{4\varepsilon}G(p,u)\,b$ and $1-G(p',u)\,b'\le e^{4\varepsilon}(1-G(p,u)\,b)$.
--
--   Items 1, 2 and 4 say that the accept/reject bit, the gate bit and their AND change by factors $e^{2\varepsilon}$, $e^{2\varepsilon}$ and $e^{4\varepsilon}$ between neighbouring samples; this is the pure-DP part of the privacy proof of Theorem 4.1. Since the hypotheses are symmetric in the two samples, the reverse inequalities follow by exchanging them.
--
--   Differences from the source:
--   - generalization: the protocol's $q_S(m,a)$, $p_S(m)$ and $U_m(r)$ → any reals with $0\le q\le p$ and the two multiplicative bounds, and any $u>0$; reason: the protocol's quantities are an instance
--   - reading: $q_S(m,a)$, $p_S(m)-q_S(m,a)$ and $p_S(m)$ change multiplicatively by at most $e^\varepsilon$; a bit is $2\varepsilon$-DP → two-sided bounds for $q$ and $p-q$ (the bound for $p$ follows); a bit's probabilities of $1$ and of $0$ each grow by at most the stated factor from one sample to the other; reason: the hypothesis for $p$ is implied by the other two; the reverse direction is the same statement with the samples exchanged
--   - encoding: $b_S(m,a)=q_S(m,a)/p_S(m)$, with value $0$ when $p_S(m)=0$ → $q/p$ in Lean, where $q/0=0$; reason: same convention
--   - generalization: the scalar inequalities for $y$ defined by $U_m(r)=y\kappa p_S(m)$ → for every real $y$; reason: the page's $y$ is an instance
-- source:
--   Du, Dwork, Tankala, Zhang, Differentially Private Verification of Distribution Properties, arXiv:2604.10819 (version of November 3, 2026, sha256 0146fa5f…), Proof of Theorem 4.1, p.15 (PDF p.18)

import Mathlib
import Definitions.Def_DPVerify_gate

set_option autoImplicit false

namespace DPVerify

/-- §4, proof of Theorem 4.1, the pure-DP display (Du, Dwork, Tankala, Zhang, *Differentially Private Verification of Distribution Properties*, arXiv:2604.10819 (version of November 3, 2026, sha256 0146fa5f…), p.15 = PDF p.18). Let `ε ≥ 0`, `κ > 0`,
`u > 0`, and let `0 ≤ q ≤ p` and `q′, p′` be such that `q′` and `p′ − q′` lie within a factor `e^ε` of
`q` and `p − q` (the joint probabilities on two neighbouring samples); then `p′` lies within a
factor `e^ε` of `p` as well. With
`b = q/p` (`0` when `p = 0`) and `G = G(p, u)`:
1. the accept/reject distribution `b` is `2ε`-DP: `b′ ≤ e^{2ε} b` and `1 − b′ ≤ e^{2ε}(1 − b)`;
2. the gate is `2ε`-DP: `G(p′, u) ≤ e^{2ε} G(p, u)` and `1 − G(p′, u) ≤ e^{2ε}(1 − G(p, u))`;
3. the printed scalar inequalities `e^{2ε}/(y² + e^{2ε}) ≤ e^{2ε}/(y² + 1)` and
   `e^{−2ε}/(y² + e^{−2ε}) ≥ e^{−2ε}/(y² + 1)` hold for every real `y`;
4. the AND of the two bits is `4ε`-DP: `G(p′, u) b′ ≤ e^{4ε} G(p, u) b` and
   `1 − G(p′, u) b′ ≤ e^{4ε}(1 − G(p, u) b)`.

**Formalization Note** Lean's `q / 0 = 0` is the page's convention "with value 0 when
`p_S(m) = 0`". The page's substitution `U_m(r) = yκp_S(m)` is the instance of item 2 that item 3
displays. The page also lists `p_S(m)` among the probabilities that change by at most `e^ε`;
that follows from the other two (`p = q + (p − q)`), so it is not a separate hypothesis. -/
theorem pure_dp_gate (ε κ u p q p' q' : ℝ) (hε : 0 ≤ ε) (hκ : 0 < κ) (hu : 0 < u)
    (hq : 0 ≤ q) (hqp : q ≤ p)
    (hq'l : Real.exp (-ε) * q ≤ q') (hq'u : q' ≤ Real.exp ε * q)
    (hr'l : Real.exp (-ε) * (p - q) ≤ p' - q') (hr'u : p' - q' ≤ Real.exp ε * (p - q)) :
    (q' / p' ≤ Real.exp (2 * ε) * (q / p) ∧
      1 - q' / p' ≤ Real.exp (2 * ε) * (1 - q / p)) ∧
    (gate κ p' u ≤ Real.exp (2 * ε) * gate κ p u ∧
      1 - gate κ p' u ≤ Real.exp (2 * ε) * (1 - gate κ p u)) ∧
    (∀ y : ℝ, Real.exp (2 * ε) / (y ^ 2 + Real.exp (2 * ε)) ≤
        Real.exp (2 * ε) * (1 / (y ^ 2 + 1)) ∧
      Real.exp (-2 * ε) * (1 / (y ^ 2 + 1)) ≤
        Real.exp (-2 * ε) / (y ^ 2 + Real.exp (-2 * ε))) ∧
    (gate κ p' u * (q' / p') ≤ Real.exp (4 * ε) * (gate κ p u * (q / p)) ∧
      1 - gate κ p' u * (q' / p') ≤ Real.exp (4 * ε) * (1 - gate κ p u * (q / p))) := by sorry

end DPVerify
