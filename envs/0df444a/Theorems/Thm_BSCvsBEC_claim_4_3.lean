-- Prove2me | Theorems.Thm_BSCvsBEC_claim_4_3
-- name    : BSCvsBEC.claim_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:40:21.945237+00:00
-- url     : https://prove2.me/theorems/91d13805-5d91-434b-8360-7404fbe5fd22
-- title:
--   Claim 4.3: $\operatorname{spec}(\sigma_{YZ})=\operatorname{spec}((1-\cos\theta)A+(\cos\theta)B)$, $A,B\succeq0$, $B\preceq qA$
-- statement:
--   Let $0\le\theta\le\pi/2$, let $|\omega_1\rangle,\dots,|\omega_q\rangle\in\mathbb C^q$ be unit vectors with $\langle\omega_i|\omega_j\rangle=\cos\theta$ for $i\ne j$, and let $P_1,\dots,P_q\succeq0$ act on a finite-dimensional register $\mathcal Z$ with $\sum_i\operatorname{Tr}P_i=1$. For the state $\sigma_{XYZ}=\sum_{i=1}^q|i\rangle\langle i|\otimes|\omega_i\rangle\langle\omega_i|\otimes P_i$ and the operators $A=\operatorname{diag}(P_1,\dots,P_q)$, $B=(\sqrt{P_i}\sqrt{P_j})_{i,j}$ on $\mathcal Z^{\oplus q}$:
--   1. $\operatorname{spec}(\sigma_{YZ})=\operatorname{spec}\big((1-\cos\theta)A+(\cos\theta)B\big)$;
--   2. $\operatorname{spec}(\sigma_{XZ})=\operatorname{spec}(A)$;
--   3. $\operatorname{spec}_+(\sigma_Z)=\operatorname{spec}_+(B)$;
--   4. $A\succeq0$, $B\succeq0$, and $B\preceq qA$.
--
--   Spectra are multisets of eigenvalues; $\operatorname{spec}_+$ keeps the positive ones. The claim writes the spectrum of a qPSC side-information state through a linear combination of two fixed positive operators, which is the form required by Heinävaara's theorem.
--
--   Differences from the source:
--   - reading: some fixed pure states (|ω_i⟩) with ⟨ω_i|ω_j⟩ = cos θ for i ≠ j → every family of unit vectors in ℂ^q with inner (ω i) (ω j) = cos θ for i ≠ j; reason: the page fixes an arbitrary such family; the statement is required for each one
--   - encoding: spec(M) = spec(N) for same-size Hermitian M, N → equal characteristic polynomials; reason: for Hermitian matrices the eigenvalue multiset determines and is determined by the characteristic polynomial
--   - encoding: spec₊(σ_Z) = spec₊(B) (different sizes) → equal multisets of positive eigenvalues (posSpec); reason: Lean convention; same instances
--   - encoding: B ⪯ qA → qA − B positive semidefinite; reason: definition of the PSD order
--   - encoding: 𝒵 finite-dimensional, 𝒵^{⊕q} → ℂ^ζ for a finite type ζ, 𝒵^{⊕q} = ℂ^{Fin q × ζ}; reason: finite-dimensional spaces are ℂ^ζ up to isomorphism
-- source:
--   J. Hązła, R. O'Donnell, BSC vs. BEC vs. PSC, manuscript of November 3, 2026 (STOC 2027 submission, preprint basis, sha256 a44ed9262ff4e01c0cbd7e204728d4ad8bf4cfda8dbf126b96022d4c84b56186), Claim 4.3 and the setting of §4.1, eq. (101), p.20

import Mathlib
import Definitions.Def_BSCvsBEC_condEntPSC
import Definitions.Def_BSCvsBEC_stYZ
import Definitions.Def_BSCvsBEC_mB

open scoped ComplexOrder

namespace BSCvsBEC

/-- **Claim 4.3 (p.20).** For `0 ≤ θ ≤ π/2`, the `q`-ary state
`σ_XYZ = ∑_{i=1}^q |i⟩⟨i| ⊗ |ω_i⟩⟨ω_i| ⊗ P_i` with `P_i ⪰ 0`, `∑ᵢ Tr P_i = 1`, and `A`, `B` of eq. (101):
`spec(σ_YZ) = spec((1 − cos θ)A + (cos θ)B)`; in particular `spec(σ_XZ) = spec(A)` and
`spec₊(σ_Z) = spec₊(B)`. Furthermore `A ⪰ 0`, `B ⪰ 0` and `B ⪯ qA`.
Hązła–O'Donnell, *BSC vs. BEC vs. PSC*, manuscript of November 3, 2026 (STOC 2027 submission,
sha256 a44ed926…), Claim 4.3 with the setting of §4.1, p.20.

**Formalization Note.** `𝒴 = ℂ^q`, `Z = ℂ^ζ`, `𝒵^{⊕q} = ℂ^{Fin q × ζ}`. Equality of spectra (as
multisets, with multiplicity) of two same-size Hermitian matrices is stated as equality of
characteristic polynomials; `spec₊` (different sizes) is `posSpec`, the multiset of positive
eigenvalues. `B ⪯ qA` is `qA − B ⪰ 0`. -/
theorem claim_4_3 {q : ℕ} (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ Real.pi / 2)
    (ω : Fin q → EuclideanSpace ℂ (Fin q)) (hω : IsQPSC θ ω)
    (ζ : Type) [Fintype ζ] [DecidableEq ζ] (P : Fin q → Matrix ζ ζ ℂ) (hP : IsSideInfo P) :
    (stYZ (fun i => ⇑(ω i)) P).charpoly =
        (((1 - Real.cos θ : ℝ) : ℂ) • mA P + ((Real.cos θ : ℝ) : ℂ) • mB P).charpoly ∧
      (stXZ P).charpoly = (mA P).charpoly ∧
      posSpec (stZ P) = posSpec (mB P) ∧
      (mA P).PosSemidef ∧ (mB P).PosSemidef ∧ ((q : ℂ) • mA P - mB P).PosSemidef := by sorry

end BSCvsBEC
