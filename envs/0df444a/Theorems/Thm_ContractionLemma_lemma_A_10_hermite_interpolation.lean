-- Prove2me | Theorems.Thm_ContractionLemma_lemma_A_10_hermite_interpolation
-- name    : ContractionLemma.lemma_A_10_hermite_interpolation
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:56:29.07319+00:00
-- url     : https://prove2.me/theorems/a849f250-107c-4e04-8932-e57c77db89c6
-- title:
--   Lemma A.10 — Hermite interpolation
-- statement:
--   Let $F$ be a polynomial of degree at most $D$, and choose an integer $m_t\ge 0$ for each point $t$ of a finite set, with $\sum_t m_t>D$. Then $F$ is determined by its first $m_t$ Taylor coefficients at each point $t$. In particular there are weights $\Lambda_{t,k}$, depending only on $D$, the points and the $m_t$, with
--
--   $$
--   F(0)=\sum_t\sum_{k<m_t}\Lambda_{t,k}F_{t,k},\qquad F_{t,k}=\frac{F^{(k)}(t)}{k!}.
--   $$
--
--   This lets the recovery of $F(0)$ use about $M$ Taylor coefficients per easy point instead of values at more points than exist.
--
--   Differences from the source:
--   - generalization: the easy points → any finite set of rationals; reason: the easy points are such a set
-- source:
--   Gajulapalli, The Contraction Lemma Beyond ETH (manuscript, sha256 049caea1…), Lemma A.10, p.62; proof pp.86–87

import Mathlib

set_option autoImplicit false

namespace ContractionLemma

open Polynomial

/-- **Lemma A.10 (Hermite interpolation)** — Gajulapalli, *The Contraction Lemma Beyond ETH*
(manuscript, sha256 049caea1…), p.62 (PDF p.65); proof pp.86–87.

Let `F` be a polynomial of degree at most `D`, and choose an integer `m_t ≥ 0` for each point
`t` of a finite set, with `∑_t m_t > D`. Then `F` is determined by its first `m_t` Taylor
coefficients `F_{t,k} = F^{(k)}(t)/k!` at each point `t`; in particular `F(0)` is a fixed
linear combination of these coefficients, whose weights depend only on `D`, the points and the
`m_t`, not on `F`.

**Formalization Note.** Polynomials over `ℚ`; `F_{t,k}` is `(taylor t F).coeff k`. The points
form any finite set of rationals (the paper applies the lemma to the easy points). -/
theorem lemma_A_10_hermite_interpolation (D : ℕ) (pts : Finset ℚ) (m : ℚ → ℕ)
    (hm : D < ∑ t ∈ pts, m t) :
    (∀ F₁ F₂ : ℚ[X], F₁.natDegree ≤ D → F₂.natDegree ≤ D →
      (∀ t ∈ pts, ∀ k < m t, (taylor t F₁).coeff k = (taylor t F₂).coeff k) → F₁ = F₂) ∧
    ∃ Λ : ℚ → ℕ → ℚ, ∀ F : ℚ[X], F.natDegree ≤ D →
      F.eval 0 = ∑ t ∈ pts, ∑ k ∈ Finset.range (m t), Λ t k * (taylor t F).coeff k := by sorry

end ContractionLemma
