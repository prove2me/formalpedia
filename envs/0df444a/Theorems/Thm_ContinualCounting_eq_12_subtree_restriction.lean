-- Prove2me | Theorems.Thm_ContinualCounting_eq_12_subtree_restriction
-- name    : ContinualCounting.eq_12_subtree_restriction
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:44:03.607989+00:00
-- url     : https://prove2.me/theorems/5dcc6e8c-02c1-42f7-ad04-72c95ea660da
-- title:
--   Eq. (12) — restriction to a subtree $\mathcal T^s$
-- statement:
--   Let $h$ be even and let $\nu$ be a probability law of $z$ on $\mathbb R^{2^h}$. There is a string $s\in\{\ell,r\}^{h/2}$ such that
--   $$\mathbb E\|z\|_\infty\ge\frac14\sum_{d=0}^{h/2-1}\sum_{u\in\mathcal T^s:\,d(u)=2d}2^{-d}(\sigma_{u,\ell}+\sigma_{u,r})$$
--   and consequently
--   $$\mathbb E\|z\|_\infty\ge\frac14\sum_{d=0}^{h/2-1}\sum_{u\in\mathcal T^s:\,d(u)=2d}2^{-d}\sigma_{u,\tilde s_{d+1}}.$$
--
--   The sum over the whole tree is thereby localized to a subtree with $\sqrt n$ leaves on which the privacy attack works.
--
--   Differences from the source:
--   - generalization: §5 assumes n is a power of 16 → every even h, n = 2^h; reason: the argument needs only that h/2 is an integer; powers of 16 are the case 4 ∣ h
--   - reading: a chain with Pr_{i∈L(T^s)}[u ∈ Anc(i)] and two equalities, ending in (12) → the first and the last inequality of the chain, for one s; reason: the equalities are computations of the proof; both inequalities are kept, so nothing is lost
--   - encoding: real expectations and σ → `lintegral` and σ in ℝ≥0∞; reason: no integrability assumption is needed and every term may be ∞
-- source:
--   Bairaktari, Dahl, Larsen, The Binary Tree Mechanism is Optimal for Differentially Private Continual Counting, arXiv:2607.00876 (sha256 986e6426…), §5, eq. (12), p.22 (PDF p.23)

import Mathlib
import Definitions.Def_ContinualCounting_InTs

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace ContinualCounting

/-- **Eq. (12) (restriction to a subtree `T^s`).** Bairaktari, Dahl, Larsen, arXiv:2607.00876 (sha256
986e6426…), §5, p.22: there is a choice of `s ∈ {ℓ, r}^{h/2}` with
`E[∥z∥∞] ≥ 1/4 · ∑_{d=0}^{h/2−1} ∑_{u∈T^s:d(u)=2d} 2^{−d}(σ_{u,ℓ} + σ_{u,r})`, and hence
`E[∥z∥∞] ≥ 1/4 · ∑_{d=0}^{h/2−1} ∑_{u∈T^s:d(u)=2d} 2^{−d} · σ_{u,s̃_{d+1}}`.

**Formalization Note.** The same `s` gives both inequalities. `∥·∥∞` is the sup norm of `Fin (2^h) → ℝ`. `h`
even is the only part of §5's standing assumption the statement needs. -/
theorem eq_12_subtree_restriction {h : ℕ} (hh : Even h) (ν : Measure (Fin (2 ^ h) → ℝ))
    [IsProbabilityMeasure ν] :
    ∃ s : Fin (h / 2) → Bool,
      1 / 4 * ∑ d ∈ Finset.range (h / 2), ∑ u ∈ evenLevel h s d,
          (2 : ℝ≥0∞)⁻¹ ^ d * (sigmaL ν u + sigmaR ν u) ≤ ∫⁻ z, ‖z‖ₑ ∂ν ∧
      1 / 4 * ∑ d ∈ Finset.range (h / 2), ∑ u ∈ evenLevel h s d,
          (2 : ℝ≥0∞)⁻¹ ^ d * sigmaTilde ν s u ≤ ∫⁻ z, ‖z‖ₑ ∂ν := by sorry

end ContinualCounting
