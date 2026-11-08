-- Prove2me | Theorems.Thm_AFIsingKS_bar17_lemma_8_1
-- name    : AFIsingKS.bar17_lemma_8_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T10:13:45.107331+00:00
-- url     : https://prove2.me/theorems/51e63cb9-e9c7-42b9-b9ee-b649c1d2db45
-- title:
--   [Bar17, Lemma 8.1] as used on p.15 — an analytic map of a disc between two rectangles
-- statement:
--   For $R>0$ let $D(R)=\{z\in\mathbb C:|z|\le R\}$. Let $a'<a\le b<b'$ be reals with $a'<0<b'$, and let $0<h<h'$. There exist $0<r<R$ and a function $\ell$, complex analytic on a neighbourhood of $D(R)$, with $\ell(0)=0$ and
--   $$[a,b]\times[-h,h]\subseteq\ell(D(r))\subseteq\ell(D(R))\subseteq[a',b']\times[-h',h'].$$
--
--   The paper uses this with $a=\beta_{\mathrm{lb}}$, $b=\beta_{\mathrm{KS}}-\delta$, $a'=2\beta_{\mathrm{lb}}$, $b'=\beta_{\mathrm{KS}}-\delta/2$, $h=\eta_0$, $h'=2\eta_0$, which gives $\mathrm{rect}(\delta,\eta_0)\subseteq\ell(D(r))\subseteq\ell(D(R))\subseteq\mathrm{rect}_+(\delta/2,2\eta_0)$. The map transports Jensen's formula from a disc to the rectangle.
--
--   Differences from the source:
--   - generalization: rect(δ, η₀) ⊆ ℓ(D(r)) ⊆ ℓ(D(R)) ⊆ rect₊(δ/2, 2η₀) for the paper’s rectangles → the same for all reals a′ < a ≤ b < b′ with a′ < 0 < b′ and 0 < h < h′; reason: the paper’s values are an instance whenever rect(δ, η₀) is nonempty, since then β_KS − δ/2 > 0
--   - encoding: ℓ : D(R) → ℂ complex analytic → `ℓ : ℂ → ℂ` with `AnalyticOnNhd ℂ ℓ (closedBall 0 R)`; reason: analyticity on a closed disc means analyticity on a neighbourhood
-- source:
--   Bencs, Huang, Lee, Liu, Regts, On Zeros and Algorithms for Disordered Systems II, arXiv:2610.40598 (held version, sha256 2a07c158…), proof of Theorem 3.1, p.15 (citing [Bar17, Lemma 8.1])

import Mathlib

open Set

namespace AFIsingKS

/-- [Bar17, Lemma 8.1] as used in the proof of Theorem 3.1 (Bencs, Huang, Lee, Liu, Regts, arXiv:2610.40598 (held version, sha256 2a07c158…), p.15), in a general form: between a closed
rectangle and a larger one around `0` there is an analytic map of a disc sending `0` to `0`.

**Formalization Note.** The paper's use is `a = β_lb`, `b = β_KS − δ`, `a' = 2β_lb`, `b' = β_KS − δ/2`,
`h = η₀`, `h' = 2η₀`, where `β_KS − δ/2 > 0` whenever `rect(δ, η₀)` is nonempty. `0` need not lie in the
inner rectangle. -/
theorem bar17_lemma_8_1 (a b a' b' h h' : ℝ) (ha : a' < a) (hab : a ≤ b) (hb : b < b')
    (ha' : a' < 0) (hb' : 0 < b') (hh : 0 < h) (hh' : h < h') :
    ∃ r R : ℝ, 0 < r ∧ r < R ∧ ∃ ℓ : ℂ → ℂ,
      AnalyticOnNhd ℂ ℓ (Metric.closedBall 0 R) ∧ ℓ 0 = 0 ∧
      {z : ℂ | z.re ∈ Icc a b ∧ z.im ∈ Icc (-h) h} ⊆ ℓ '' Metric.closedBall 0 r ∧
      ℓ '' Metric.closedBall 0 R ⊆ {z : ℂ | z.re ∈ Icc a' b' ∧ z.im ∈ Icc (-h') h'} := by sorry

end AFIsingKS
