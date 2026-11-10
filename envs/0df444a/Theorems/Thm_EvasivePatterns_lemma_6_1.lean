-- Prove2me | Theorems.Thm_EvasivePatterns_lemma_6_1
-- name    : EvasivePatterns.lemma_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:26:21.939198+00:00
-- url     : https://prove2.me/theorems/d6a29e46-4994-4db6-be53-6c49f00f8b90
-- title:
--   Lemma 6.1 — eventual nonvanishing of the coefficients of $1/V$
-- statement:
--   Let $V \in \mathbb Q[z]$ satisfy $V(0) = 1$ and have a simple complex root $\alpha$ that is isolated as in (10): every root $\beta$ of $V$ for which $\beta/\alpha$ is a root of unity equals $\alpha$. Then the coefficients
--   $$
--   b_n = [z^n]\, \frac{1}{V(z)}
--   $$
--   are nonzero for all sufficiently large $n$.
--
--   Differences from the source:
--   - encoding: 1/V(z) and its coefficients b_n → the inverse of V in ℚ⟦z⟧; reason: V(0) = 1, so V is invertible
-- source:
--   Faro, Marino, Pavone, A Complete Characterization of Eventually Evasive Binary Patterns, manuscript (Nov. 2026; sha256 e91deef3…), Lemma 6.1, p.9 (PDF p.10), lines 282–283

import Mathlib

namespace EvasivePatterns

/-- **Lemma 6.1 (Eventual nonvanishing).** Let `V ∈ ℚ[z]` satisfy `V(0) = 1` and have a simple root
`α` isolated as in (10). Then the coefficients `b_n = [zⁿ] 1/V(z)` are nonzero for all sufficiently
large `n`.

Source: S. Faro, F. P. Marino, A. Pavone, *A Complete Characterization of Eventually Evasive Binary
Patterns*, manuscript (Nov. 2026), Lemma 6.1, printed p. 9 (PDF p. 10), lines 282–283; condition (10), printed p. 8
(PDF p. 9), line 254.

**Formalization Note** Roots are complex (`V` cast to `ℂ[z]`); "simple" is root multiplicity
exactly `1`; "isolated as in (10)": every complex root `β` of `V` with `(β/α)ⁿ = 1` for some
`n > 0` equals `α`. `1/V` is the inverse of `V` in `ℚ⟦z⟧` (`V(0) = 1`). -/
theorem lemma_6_1 (V : Polynomial ℚ) (hV0 : V.coeff 0 = 1) (α : ℂ)
    (hα : (V.map (algebraMap ℚ ℂ)).IsRoot α)
    (hsimple : (V.map (algebraMap ℚ ℂ)).rootMultiplicity α = 1)
    (hiso : ∀ β : ℂ, (V.map (algebraMap ℚ ℂ)).IsRoot β →
      (∃ n : ℕ, 0 < n ∧ (β / α) ^ n = 1) → β = α) :
    ∃ N : ℕ, ∀ n ≥ N, PowerSeries.coeff n ((V : PowerSeries ℚ)⁻¹) ≠ 0 := by sorry

end EvasivePatterns
