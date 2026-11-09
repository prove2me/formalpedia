-- Prove2me | Theorems.Thm_BSCvsBEC_theorem_4_1
-- name    : BSCvsBEC.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:35:56.487285+00:00
-- url     : https://prove2.me/theorems/c78ce8ed-4d00-4a69-af91-26d8c7497f91
-- title:
--   Theorem 4.1: $H(Y)\ge\mathbb E_{R\sim\sin^2\theta}H(X_R)$ for the $\mathrm{PSC}_\theta$ output
-- statement:
--   Let $0\le\theta\le\pi/2$ and let $|\omega_0\rangle,|\omega_1\rangle\in\mathbb C^2$ be unit vectors with $\langle\omega_0|\omega_1\rangle=\cos\theta$. Let $X\in\mathbb F_2^n$ be any random variable, and let $Y$ be the mixed state $\sigma_Y=\sum_xP_X(x)|\omega_x\rangle\langle\omega_x|$ arising from passing $X$ through $\mathrm{PSC}_\theta$. Then
--   $$H(Y)\ \ge\ \mathbb E_{R\sim\sin^2\theta}\,H(X_R),$$
--   where $R\subseteq[n]$ contains each coordinate independently with probability $\sin^2\theta$ and $H$ is the von Neumann (resp. Shannon) entropy in bits.
--
--   By the two §4 identities, this is equivalent to the "if" direction of Theorem 1.3 at $\lambda=\cos^2\theta$.
--
--   Differences from the source:
--   - reading: some fixed pure states |ω₀⟩, |ω₁⟩ with ⟨ω₀|ω₁⟩ = cos θ → every pair of unit vectors in ℂ² with inner ω₀ ω₁ = cos θ; reason: the page fixes an arbitrary such pair; the statement is required for each one
--   - encoding: a random variable X on a finite set → its pmf P with IsPMF P; reason: Lean convention; same instances
-- source:
--   J. Hązła, R. O'Donnell, BSC vs. BEC vs. PSC, manuscript of November 3, 2026 (STOC 2027 submission, preprint basis, sha256 a44ed9262ff4e01c0cbd7e204728d4ad8bf4cfda8dbf126b96022d4c84b56186), Theorem 4.1, eq. (95), p.19

import Mathlib
import Definitions.Def_BSCvsBEC_shannon
import Definitions.Def_BSCvsBEC_expectSubset
import Definitions.Def_BSCvsBEC_condEntPSC

namespace BSCvsBEC

/-- **Theorem 4.1 (p.19).** Let `X ∈ F₂ⁿ` be any random variable and `Y` the mixed state obtained by
passing `X` through `PSC_θ`. Then `H(Y) ≥ E_{R∼sin²θ} H(X_R)` (eq. (95)).
Hązła–O'Donnell, *BSC vs. BEC vs. PSC*, manuscript of November 3, 2026 (STOC 2027 submission,
sha256 a44ed926…), Theorem 4.1, p.19.

**Formalization Note.** `X` has pmf `P`; `H(Y)` is the von Neumann entropy (bits) of
`σ_Y = ∑ₓ P(x)|ω_x⟩⟨ω_x|`; `R` contains each coordinate independently with probability `sin²θ`.
The pair `ω` is any pair with `IsPSCPair θ ω`. -/
theorem theorem_4_1 (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ Real.pi / 2)
    (ω : Fin 2 → EuclideanSpace ℂ (Fin 2)) (hω : IsPSCPair θ ω) {n : ℕ}
    (P : (Fin n → Fin 2) → ℝ) (hP : IsPMF P) :
    expectSubset (Real.sin θ ^ 2) n (fun R => shannon (margR R P)) ≤
      ShadowTomography.QuantumLB.vnEntropy (outState P (pscVec ω)) := by sorry

end BSCvsBEC
