-- Prove2me | Theorems.Thm_AgreementTop736_Exact_sec3_1_regularizer_comparison
-- name    : AgreementTop736.Exact.sec3_1_regularizer_comparison
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:58:10.783929+00:00
-- url     : https://prove2.me/theorems/a10cdbba-9c68-4029-9c1e-c5398c4b78f6
-- title:
--   Section 3.1, p.10 — $z(f(m)-f(u))^2=\frac{z(m-u)^2}{(m+a)(u+a)(\sqrt{m+a}+\sqrt{u+a})^2}\le\frac{\rho(m-u)^2}{(m+a)^2}$
-- statement:
--   Let $\rho>0$ and $a>0$, and let $f(u)=(u+a)^{-1/2}$. For real $m\ge0$, $z\ge0$ and $u=z/\rho$,
--   $$z\big(f(m)-f(u)\big)^2=\frac{z(m-u)^2}{(m+a)(u+a)\big(\sqrt{m+a}+\sqrt{u+a}\big)^2}\ \le\ \frac{\rho(m-u)^2}{(m+a)^2}.$$
--
--   Applied with $m=m_K$ and $z=Z(K,H)$, this turns the residual $R(K,H)$ into the variance of $Z$ given $K$, which is how hypothesis 2 enters the proof.
--
--   Differences from the source:
--   - generalization: m the integer error count m_K → any real m ≥ 0; reason: the display is an identity and inequality of reals; it specializes to m = m_K
--   - encoding: f(u) = (u + a)^{-1/2} → 1 / √(u + a); reason: equal for u + a > 0, the only case used
--   - generalization: ρ = n/N with 0 < n < N, hence 0 < ρ < 1 → any real ρ > 0; reason: the scalar comparison uses only positivity of ρ and specializes to the paper's ratio
-- source:
--   Tali Kaufman, Huy Tuan Pham, Exact Agreement Expansion up to the Top via Non-polarity, STOC 2027 submission #736 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/736.pdf (source.pdf sha256 04ba433ef4a669f9160de90c29bfff3152be2a1d08e50186f52e514c298f5d49), p.10, Section 3.1, display after 'Let R(K, H) = φ(K)|_H − ψ(K, H)'

import Mathlib
import Definitions.Def_AgreementTop736_Exact_Regularized

namespace AgreementTop736.Exact

/-- §3.1, p.10, display after "Let R(K, H) = φ(K)|_H − ψ(K, H)": for `ρ > 0`, `a > 0`, `m ≥ 0`,
`z ≥ 0` and `u = z/ρ`, with `f(u) = (u + a)^{-1/2}`,
`z (f(m) − f(u))² = z (m − u)² / ((m + a)(u + a)(√(m + a) + √(u + a))²) ≤ ρ (m − u)² / (m + a)²`. -/
theorem sec3_1_regularizer_comparison {ρ a m z u : ℝ} (hρ : 0 < ρ) (ha : 0 < a) (hm : 0 ≤ m)
    (hz : 0 ≤ z) (hu : u = z / ρ) :
    z * (fReg a m - fReg a u) ^ 2 =
      z * (m - u) ^ 2 / ((m + a) * (u + a) * (Real.sqrt (m + a) + Real.sqrt (u + a)) ^ 2) ∧
    z * (m - u) ^ 2 / ((m + a) * (u + a) * (Real.sqrt (m + a) + Real.sqrt (u + a)) ^ 2) ≤
      ρ * (m - u) ^ 2 / (m + a) ^ 2 := by sorry

end AgreementTop736.Exact
