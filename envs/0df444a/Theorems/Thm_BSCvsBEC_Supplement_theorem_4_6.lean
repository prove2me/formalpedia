-- Prove2me | Theorems.Thm_BSCvsBEC_Supplement_theorem_4_6
-- name    : BSCvsBEC.Supplement.theorem_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:41:47.074354+00:00
-- url     : https://prove2.me/theorems/4a951275-0bef-45c7-b6da-33dee2b3e6fa
-- title:
--   Theorem 4.6 — binary Rényi PSC–BEC comparison $H_\alpha(YZ)_\sigma\ge\mathbb E_{R\sim\tau_\alpha(\theta)}H_\alpha(X_RZ)_\sigma$
-- statement:
--   Let $1<\alpha<\infty$, $0\le\theta\le\pi/2$, let $|\omega_0\rangle,|\omega_1\rangle\in\mathbb C^2$ be unit vectors with $\langle\omega_0|\omega_1\rangle=\cos\theta$, and let
--   $$\sigma_{XYZ}=\sum_{x\in\mathbb F_2^n}|x\rangle\langle x|\otimes|\omega_x\rangle\langle\omega_x|\otimes P_x,\qquad P_x\succeq0,\quad\sum_x\mathrm{Tr}\,P_x=1,$$
--   with side information on a register $Z$ of any finite dimension. Then
--   $$H_\alpha(YZ)_\sigma\ \ge\ \mathbb E_{R\sim\tau_\alpha(\theta)}H_\alpha(X_RZ)_\sigma,$$
--   where $\tau_\alpha(\theta)=1-\lambda^*(\alpha,2,\cos\theta)$ and $R\subseteq[n]$ contains each coordinate independently with probability $\tau_\alpha(\theta)$. For $\alpha\ge2$,
--   $$\tau_\alpha(\theta)=H_\alpha\Big(\mathrm{Ber}\Big(\frac{1-\cos\theta}2\Big)\Big);$$
--   for $1<\alpha<2$ it is given by the sharp one-coordinate variational constant of Theorem 2.7.
--
--   This is the Rényi analogue of the paper's main inequality (Theorem 4.1 is the case $\alpha\to1$, trivial $Z$). Entropies are Rényi entropies of spectra, in bits.
--
--   **Formalization Note** The two displayed claims are the two conjuncts; $\mathrm{Ber}(p)$ is the pmf $(1-p,p)$.
--
--   Differences from the source:
--   - reading: some fixed pure states |ω₀⟩, |ω₁⟩ with ⟨ω₀|ω₁⟩ = cos θ → every pair of unit vectors in ℂ² with inner ω₀ ω₁ = cos θ (IsPSCPair θ ω); reason: the page fixes an arbitrary such pair; the statement is required for each one
--   - encoding: a side information register Z of any finite dimension, P_x ⪰ 0, ∑ₓ Tr P_x = 1 → Z = ℂ^ζ for every finite type ζ, with IsSideInfo P; reason: Lean convention; same instances
--   - encoding: the Rényi order 1 < α < ∞ → a real α > 1 used as ENNReal.ofReal α in BSCvsBEC.renyi; reason: same values of α
-- source:
--   J. Hązła, R. O'Donnell, BSC vs. BEC vs. PSC, manuscript of November 3, 2026 (STOC 2027 submission, preprint basis, sha256 a44ed9262ff4e01c0cbd7e204728d4ad8bf4cfda8dbf126b96022d4c84b56186), Theorem 4.6, eq. (113), p.22; τ_α(θ) := 1 − λ*(α, 2, cos θ), p.22

import Mathlib
import Definitions.Def_BSCvsBEC_expectSubset
import Definitions.Def_BSCvsBEC_condEntPSC
import Definitions.Def_BSCvsBEC_renyi
import Definitions.Def_BSCvsBEC_stYZ
import Definitions.Def_BSCvsBEC_Supplement_lamStarB

namespace BSCvsBEC.Supplement

/-- **Theorem 4.6 (p.22, binary Rényi PSC–BEC comparison).** Let `1 < α < ∞`, `0 ≤ θ ≤ π/2`, and let
`σ_XYZ = ∑_{x∈F₂ⁿ} |x⟩⟨x| ⊗ |ω_x⟩⟨ω_x| ⊗ P_x`, `P_x ⪰ 0`, `∑ₓ Tr P_x = 1`. Then
`H_α(YZ)_σ ≥ E_{R∼τ_α(θ)} H_α(X_R Z)_σ` (eq. (113)). For `α ≥ 2`, `τ_α(θ) = H_α(Ber((1 − cos θ)/2))`;
for `1 < α < 2` it is given by the sharp one-coordinate variational constant of Theorem 2.7.
Hązła–O'Donnell, *BSC vs. BEC vs. PSC*, manuscript of November 3, 2026 (STOC 2027 submission,
sha256 a44ed926…), Theorem 4.6, eq. (113), p.22, with `τ_α(θ) := 1 − λ*(α, 2, cos θ)` (p.22).

**Formalization Note.** `α` is real, used as the Rényi order `ENNReal.ofReal α`; `τ_α(θ)` is `tauBin α θ`.
`Z = ℂ^ζ` for an arbitrary finite type `ζ` with any `IsSideInfo` family; every `n`; every pair `ω` with
`IsPSCPair θ ω`. `H_α` is the published `renyi` (bits). The second conjunct is the page's `α ≥ 2`
formula, with `Ber(p)` the pmf `(1 − p, p)` on `F₂`. -/
theorem theorem_4_6 (α : ℝ) (hα : 1 < α) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ Real.pi / 2)
    (ω : Fin 2 → EuclideanSpace ℂ (Fin 2)) (hω : BSCvsBEC.IsPSCPair θ ω)
    (n : ℕ) (ζ : Type) [Fintype ζ] [DecidableEq ζ] (P : (Fin n → Fin 2) → Matrix ζ ζ ℂ)
    (hP : BSCvsBEC.IsSideInfo P) :
    BSCvsBEC.expectSubset (tauBin α θ) n
        (fun R => BSCvsBEC.renyi (ENNReal.ofReal α) (BSCvsBEC.stXRZ R P)) ≤
      BSCvsBEC.renyi (ENNReal.ofReal α) (BSCvsBEC.stYZ (BSCvsBEC.pscVec ω) P) ∧
    (2 ≤ α → tauBin α θ =
      renyiP (ENNReal.ofReal α) ![1 - (1 - Real.cos θ) / 2, (1 - Real.cos θ) / 2]) := by sorry

end BSCvsBEC.Supplement
