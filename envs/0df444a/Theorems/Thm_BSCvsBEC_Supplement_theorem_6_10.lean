-- Prove2me | Theorems.Thm_BSCvsBEC_Supplement_theorem_6_10
-- name    : BSCvsBEC.Supplement.theorem_6_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:43:19.010515+00:00
-- url     : https://prove2.me/theorems/7490bf59-6e24-4406-b22a-feb73ddb270b
-- title:
--   Theorem 6.10 — Conjecture 6.6 near the uniform distribution
-- statement:
--   Fix $n\ge1$ and $0<\theta<\pi/2$, write $p=(1-\cos\theta)/2$ and let $h$ be the binary entropy function (bits). There exists $\epsilon_0=\epsilon_0(\theta,n)>0$ such that for every pair of unit vectors $|\omega_0\rangle,|\omega_1\rangle\in\mathbb C^2$ with $\langle\omega_0|\omega_1\rangle=\cos\theta$, every $0\le\lambda\le1-\sin\theta$ and every random $X\in\mathbb F_2^n$ with $|P_X(x)-2^{-n}|\le\epsilon_0$ for all $x\in\mathbb F_2^n$, the output state $\sigma_Y=\sum_xP_X(x)|\omega_x\rangle\langle\omega_x|$ of $\mathrm{PSC}_\theta$ satisfies
--   $$H(\sigma_Y)\ \ge\ \mathbb E_{S\sim1-\lambda}H(X_S)-(1-\lambda-h(p))\,n .$$
--   Here $H(\sigma_Y)$ is the von Neumann entropy, $S\subseteq[n]$ contains each coordinate independently with probability $1-\lambda$, and $H(X_S)$ is the Shannon entropy of the restriction.
--
--   This proves Conjecture 6.6 in a neighbourhood of the uniform distribution, the region where the classical analogue would be expected to fail first.
--
--   Differences from the source:
--   - reading: ε₀ = ε₀(θ, n) → ∃ ε₀ > 0 chosen before ω, λ and P; reason: ε₀ depends only on θ and n; all pairs ω with the same inner product give unitarily equivalent states
--   - reading: some fixed pure states |ω₀⟩, |ω₁⟩ with ⟨ω₀|ω₁⟩ = cos θ → every pair of unit vectors in ℂ² with inner ω₀ ω₁ = cos θ (IsPSCPair θ ω); reason: the page fixes an arbitrary such pair; the statement is required for each one
--   - encoding: a random variable X on a finite set → its pmf P with IsPMF P; reason: Lean convention; same instances
-- source:
--   J. Hązła, R. O'Donnell, BSC vs. BEC vs. PSC, manuscript of November 3, 2026 (STOC 2027 submission, preprint basis, sha256 a44ed9262ff4e01c0cbd7e204728d4ad8bf4cfda8dbf126b96022d4c84b56186), Theorem 6.10, p.29; p = (1 − cos θ)/2: §6.3, p.27; h: p.2

import Mathlib
import Definitions.Def_ShadowTomography_QuantumLB_vnEntropy
import Definitions.Def_BSCvsBEC_shannon
import Definitions.Def_BSCvsBEC_expectSubset
import Definitions.Def_BSCvsBEC_condEntPSC

namespace BSCvsBEC.Supplement

/-- **Theorem 6.10 (p.29).** Fix `n ≥ 1` and `0 < θ < π/2` and let `0 ≤ λ ≤ 1 − sin θ`. Let `X ∈ F₂ⁿ`
and send `X` over `PSC_θ`, resulting in the joint state `σ_XY`. There exists `ε₀ = ε₀(θ, n) > 0` such
that if `|P_X(x) − 2^{−n}| ≤ ε₀` for every `x ∈ F₂ⁿ`, then `H(σ_Y) ≥ E_{S∼1−λ} H(X_S) − (1 − λ − h(p))n`.
Hązła–O'Donnell, *BSC vs. BEC vs. PSC*, manuscript of November 3, 2026 (STOC 2027 submission,
sha256 a44ed926…), Theorem 6.10, p.29, with `p = (1 − cos θ)/2` (§6.3, p.27) and `h` the binary entropy (p.2).

**Formalization Note.** `ε₀` is chosen before the pair `ω`, `λ` and the pmf `P` (it depends only on
`θ` and `n`). `H(σ_Y)` is the von Neumann entropy in bits of `σ_Y = ∑ₓ P(x)|ω_x⟩⟨ω_x|`;
`h(p) = shannon ![p, 1 − p]` in bits; `S` contains each coordinate independently with probability
`1 − λ`. -/
theorem theorem_6_10 (n : ℕ) (hn : 1 ≤ n) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ (ω : Fin 2 → EuclideanSpace ℂ (Fin 2)), BSCvsBEC.IsPSCPair θ ω →
      ∀ (lam : ℝ), 0 ≤ lam → lam ≤ 1 - Real.sin θ →
      ∀ (P : (Fin n → Fin 2) → ℝ), BSCvsBEC.IsPMF P →
        (∀ x, |P x - ((2 : ℝ) ^ n)⁻¹| ≤ ε₀) →
        BSCvsBEC.expectSubset (1 - lam) n (fun S => BSCvsBEC.shannon (BSCvsBEC.margR S P)) -
            (1 - lam - BSCvsBEC.shannon
              ![(1 - Real.cos θ) / 2, 1 - (1 - Real.cos θ) / 2]) * n ≤
          ShadowTomography.QuantumLB.vnEntropy
            (BSCvsBEC.outState P (BSCvsBEC.pscVec ω)) := by sorry

end BSCvsBEC.Supplement
