-- Prove2me | Theorems.Thm_CubicPermFPRAS_eq_15_update
-- name    : CubicPermFPRAS.eq_15_update
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T10:00:00.593691+00:00
-- url     : https://prove2.me/theorems/af5a9597-ac69-45bf-a358-c88b1dba0e88
-- title:
--   Eq. (15), p.18 — the anchor-weight update recovers $w^*$ and has ratio in $[9/11,11/9]$
-- statement:
--   Let $\lambda$ be positive activities, $r$ an anchor, $w(r,\cdot)$ positive anchor weights, $B$ the rescaled matrix and $p_v=\pi_B(\mathcal N(r,v))$. For positive estimates $\hat p_v$ set
--   $$\tilde w(r,v)=\frac{w(r,v)W(r,v)}{\hat p_v},\qquad w'(r,v)=\tilde w(r,v)\sum_{z\in V_2}\frac{\lambda(r,z)}{\tilde w(r,z)}.\tag{15}$$
--   Then:
--
--   1. $\sum_z\lambda(r,z)/w^*(r,z)=1$;
--   2. with exact frequencies $\hat p=p$, the update returns $w'(r,\cdot)=w^*(r,\cdot)$;
--   3. if $|\hat p_v-p_v|\le p_v/10$ for every $v$, then $w'(r,v)/w^*(r,v)\in[9/11,11/9]$ for every $v$.
--
--   So the updated anchor weights are accurate, with an error that depends only on the current frequency estimates.
--
--   Differences from the source:
--   - generalization: supplied $\alpha$-rough anchor weights → every positive anchor weight vector; reason: the identity $w(r,v)W(r,v)/p_v\propto w^*(r,v)$ behind the update uses only positivity; rough weights are positive
--   - encoding: "relative frequency errors of at most $1/10$" → $|\hat p_v-p_v|\le p_v/10$ for every $v$; reason: the same condition
-- source:
--   Chen, Guo, Vigoda, Yang, An Õ(n³)-time FPRAS for the Permanent, arXiv:2609.20717 (held version, sha256 9e14f335…), Eq. (15) and the two sentences after it, p.18 (PDF 20)

import Mathlib
import Definitions.Def_CubicPermFPRAS_permFPRAS

set_option autoImplicit false

namespace CubicPermFPRAS

/-- **The anchor-weight update, Eq. (15)**, p.18 (PDF 20), with the two sentences after it,
X. Chen, H. Guo, E. Vigoda, X. Yang, *An Õ(n³)-time FPRAS for the Permanent*, arXiv:2609.20717 (held version, sha256 9e14f335…).

For positive frequency estimates `p̂_v`, set `w̃(r,v) = w(r,v)W(r,v)/p̂_v` and
`w'(r,v) = w̃(r,v) ∑_z λ(r,z)/w̃(r,z)`. Expanding the permanent along row `r` gives
`∑_z λ(r,z)/w*(r,z) = 1`, so the normalization recovers `w*` from exact frequencies; relative
frequency errors of at most `1/10` give `w'(r,v)/w*(r,v) ∈ [9/11, 11/9]`.

**Formalization Note.** `p_v = π_B(N(r,v))` are the exact frequencies. The statement is for
every positive anchor weight vector `w(r,·)` (the paper's are `α`-rough); the identity behind it
uses only positivity. -/
theorem eq_15_update (n : ℕ) (hn : 1 ≤ n) (lam : Matrix (Fin n) (Fin n) ℝ)
    (hlam : ∀ u v, 0 < lam u v) (r : Fin n) (w : Fin n → ℝ) (hw : ∀ v, 0 < w v) :
    ∑ z, lam r z / idealHW lam r z = 1 ∧
    anchorUpdate lam (Bmat lam w) r w (holeProb (Bmat lam w) r) = idealHW lam r ∧
    ∀ phat : Fin n → ℝ, (∀ v, 0 < phat v) →
      (∀ v, |phat v - holeProb (Bmat lam w) r v| ≤ holeProb (Bmat lam w) r v / 10) →
      ∀ v, 9 / 11 ≤ anchorUpdate lam (Bmat lam w) r w phat v / idealHW lam r v ∧
        anchorUpdate lam (Bmat lam w) r w phat v / idealHW lam r v ≤ 11 / 9 := by sorry

end CubicPermFPRAS
