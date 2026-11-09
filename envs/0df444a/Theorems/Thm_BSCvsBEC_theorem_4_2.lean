-- Prove2me | Theorems.Thm_BSCvsBEC_theorem_4_2
-- name    : BSCvsBEC.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:40:14.79121+00:00
-- url     : https://prove2.me/theorems/9d7d867b-86cd-45c8-b577-4d39c77d87f2
-- title:
--   Theorem 4.2: $H(YZ)\ge\sin^2\theta\,H(XZ)+\cos^2\theta\,H(Z)$
-- statement:
--   Let $0\le\theta\le\pi/2$ and $|\omega_0\rangle,|\omega_1\rangle\in\mathbb C^2$ unit vectors with $\langle\omega_0|\omega_1\rangle=\cos\theta$. Let $Z$ be an arbitrary finite-dimensional ("side information") register, and let
--   $$\sigma_{XYZ}=\sum_{b\in\mathbb F_2}|b\rangle\langle b|\otimes|\omega_b\rangle\langle\omega_b|\otimes P_b,\qquad P_0,P_1\succeq0,\ \operatorname{Tr}(P_0+P_1)=1.$$
--   Then
--   $$H(YZ)_\sigma\ \ge\ (\sin^2\theta)\,H(XZ)_\sigma+(\cos^2\theta)\,H(Z)_\sigma,$$
--   with $H$ the von Neumann entropy in bits.
--
--   This one-bit inequality, tensorized by Lemma 2.3 (with $\alpha=1$, $\lambda=\sin^2\theta$), gives Theorem 4.1 and hence Theorem 1.3.
--
--   Differences from the source:
--   - reading: some fixed pure states |ω₀⟩, |ω₁⟩ with ⟨ω₀|ω₁⟩ = cos θ → every pair of unit vectors in ℂ² with inner ω₀ ω₁ = cos θ; reason: the page fixes an arbitrary such pair; the statement is required for each one
--   - encoding: an arbitrary finite-dimensional register Z → ℂ^ζ for an arbitrary finite type ζ; reason: finite-dimensional registers are ℂ^ζ up to isomorphism
-- source:
--   J. Hązła, R. O'Donnell, BSC vs. BEC vs. PSC, manuscript of November 3, 2026 (STOC 2027 submission, preprint basis, sha256 a44ed9262ff4e01c0cbd7e204728d4ad8bf4cfda8dbf126b96022d4c84b56186), Theorem 4.2, eqs. (99)–(100), p.19

import Mathlib
import Definitions.Def_BSCvsBEC_condEntPSC
import Definitions.Def_BSCvsBEC_stYZ

namespace BSCvsBEC

/-- **Theorem 4.2 (p.19).** Let `Z` be an arbitrary finite-dimensional side information register and
`σ_XYZ = ∑_{b∈F₂} |b⟩⟨b| ⊗ |ω_b⟩⟨ω_b| ⊗ P_b` with `P₀, P₁ ⪰ 0`, `Tr(P₀ + P₁) = 1` (eq. (99)). Then
`H(YZ)_σ ≥ (sin²θ) H(XZ)_σ + (cos²θ) H(Z)_σ` (eq. (100)).
Hązła–O'Donnell, *BSC vs. BEC vs. PSC*, manuscript of November 3, 2026 (STOC 2027 submission,
sha256 a44ed926…), Theorem 4.2, p.19.

**Formalization Note.** `Z = ℂ^ζ` for an arbitrary finite type `ζ`; `H` is the von Neumann entropy in
bits; `σ_YZ = ∑_b |ω_b⟩⟨ω_b| ⊗ P_b`, `σ_XZ = ∑_b |b⟩⟨b| ⊗ P_b`, `σ_Z = P₀ + P₁`. The pair `ω` is any
pair with `IsPSCPair θ ω`. -/
theorem theorem_4_2 (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ Real.pi / 2)
    (ω : Fin 2 → EuclideanSpace ℂ (Fin 2)) (hω : IsPSCPair θ ω)
    (ζ : Type) [Fintype ζ] [DecidableEq ζ] (P : Fin 2 → Matrix ζ ζ ℂ) (hP : IsSideInfo P) :
    Real.sin θ ^ 2 * ShadowTomography.QuantumLB.vnEntropy (stXZ P) +
        Real.cos θ ^ 2 * ShadowTomography.QuantumLB.vnEntropy (stZ P) ≤
      ShadowTomography.QuantumLB.vnEntropy (stYZ (fun b => ⇑(ω b)) P) := by sorry

end BSCvsBEC
