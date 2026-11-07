-- Prove2me | Theorems.Thm_DetParamSVP_eq_11_parameters
-- name    : DetParamSVP.eq_11_parameters
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:51:44.838792+00:00
-- url     : https://prove2.me/theorems/9e74c285-b080-4e97-8afd-6b9429104311
-- title:
--   Proof of Theorem 3.5, Eq. (11) — integers $\gamma\ge2$, $c\ge1$ with $\gamma^p/2+8\le c^p$ and $\gamma\'c<\gamma$
-- statement:
--   Let $p\ge1$ and $1\le\gamma'<2^{1/p}$. As $\gamma\to\infty$ through the integers,
--
--   $$\frac{\lceil(\gamma^p/2+8)^{1/p}\rceil}{\gamma}\longrightarrow 2^{-1/p}<\frac1{\gamma'} .$$
--
--   Consequently, for all sufficiently large integers $\gamma$, the integer $c=\lceil(\gamma^p/2+8)^{1/p}\rceil$ satisfies
--
--   $$\gamma\ge2,\qquad c\ge1,\qquad \gamma^p/2+8\le c^p,\qquad \gamma'c<\gamma.\tag{11}$$
--
--   These are the fixed integers of the reduction in Theorem 3.5.
--
--   **Formalization Note** Three conclusions: the limit, the strict inequality $2^{-1/p}<1/\gamma'$, and the four conditions of (11) for all sufficiently large $\gamma$.
--
--   Differences from the source:
--   - encoding: "as γ tends to infinity through the positive integers", "for all sufficiently large integers γ" → Filter.Tendsto along atTop on ℕ, and ∀ᶠ γ in atTop; reason: the value at γ = 0 does not affect either
-- source:
--   Hirahara–Lin–Liu–Ogitsuka, Deterministic Parameterized Inapproximability of the Shortest Vector and Minimum Distance Problems, STOC 2027 submission (manuscript sha256 4584f5e2…), proof of Theorem 3.5, Eq. (11), p.23

import Mathlib

set_option autoImplicit false

namespace DetParamSVP

/-- **Proof of Theorem 3.5, Eq. (11).** For `p ≥ 1` and `1 ≤ γ' < 2^{1/p}`: as `γ → ∞` through the
integers, `⌈(γ^p/2 + 8)^{1/p}⌉ / γ → 2^{−1/p} < 1/γ'`; hence, for all sufficiently large integers
`γ`, taking `c = ⌈(γ^p/2 + 8)^{1/p}⌉` gives `γ ≥ 2`, `c ≥ 1`, `γ^p/2 + 8 ≤ c^p` and `γ'c < γ`
(11).

Hirahara–Lin–Liu–Ogitsuka, *Deterministic Parameterized Inapproximability of the Shortest Vector
and Minimum Distance Problems*, STOC 2027 submission (manuscript sha256 4584f5e2…), proof of Theorem 3.5, Eq. (11), p.23.

**Formalization Note.** Three conclusions: the limit (a `Filter.Tendsto` along `ℕ`), the strict
inequality `2^{−1/p} < 1/γ'`, and the four conditions of (11) for all sufficiently large `γ ∈ ℕ`
(`∀ᶠ γ in atTop`). Powers with real exponents are `Real.rpow`; `⌈·⌉₊` is `Nat.ceil`. -/
theorem eq_11_parameters (p γ' : ℝ) (hp : 1 ≤ p) (hγ'₁ : 1 ≤ γ') (hγ' : γ' < 2 ^ (1 / p)) :
    Filter.Tendsto (fun γ : ℕ => (⌈((γ : ℝ) ^ p / 2 + 8) ^ (1 / p)⌉₊ : ℝ) / γ) Filter.atTop
        (nhds ((2 : ℝ) ^ (-1 / p))) ∧
      (2 : ℝ) ^ (-1 / p) < 1 / γ' ∧
      ∀ᶠ γ : ℕ in Filter.atTop,
        2 ≤ γ ∧ 1 ≤ ⌈((γ : ℝ) ^ p / 2 + 8) ^ (1 / p)⌉₊ ∧
        (γ : ℝ) ^ p / 2 + 8 ≤ (⌈((γ : ℝ) ^ p / 2 + 8) ^ (1 / p)⌉₊ : ℝ) ^ p ∧
        γ' * ⌈((γ : ℝ) ^ p / 2 + 8) ^ (1 / p)⌉₊ < γ := by sorry

end DetParamSVP
