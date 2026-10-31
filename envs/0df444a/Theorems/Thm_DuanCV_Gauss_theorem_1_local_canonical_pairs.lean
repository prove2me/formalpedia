-- Prove2me | Theorems.Thm_DuanCV_Gauss_theorem_1_local_canonical_pairs
-- name    : DuanCV.Gauss.theorem_1_local_canonical_pairs
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:57:52.211932+00:00
-- url     : https://prove2.me/theorems/2a061d20-a089-4374-bdd9-c0f23f041906
-- title:
--   Remark after Theorem 1 — the bound (3) for local canonical pairs (symplectic and Stone–von Neumann) and either sign
-- statement:
--   Let $\rho$ be a separable two-mode state, $a\neq0$ real and $s,t\in\{1,-1\}$. Put
--
--   $$\hat u=|a|\hat x_1+\frac sa\hat x_2,\qquad \hat v=|a|\hat p_1+\frac ta\hat p_2.$$
--
--   Then the following two statements hold.
--
--   1. For all $2\times2$ real symplectic matrices $S_1,S_2$, the bound $\langle(\Delta\hat u')^2\rangle_\rho+\langle(\Delta\hat v')^2\rangle_\rho\ge a^2+1/a^2$ holds, where $\hat u',\hat v'$ are obtained by replacing $(\hat x_j,\hat p_j)$ with the canonical pair given by the columns of $S_j$.
--   2. For all isometries $W_1,W_2:\ell^2(\mathbb N)\to\ell^2(\mathbb N)\otimes\ell^2(\mathbb N)$, the same bound holds when $(\hat x_j,\hat p_j)$ is replaced by $(W_j^\dagger(\hat x_j\otimes I)W_j,\ W_j^\dagger(\hat p_j\otimes I)W_j)$; equivalently, the variances of $\hat u,\hat v$ are taken in the state $\operatorname{tr}_E[(W_1\otimes W_2)\rho(W_1\otimes W_2)^\dagger]$. Every Weyl-regular local canonical pair is of this form, and the arbitrary local unitary $U_1\otimes U_2$ of the paper is the case $W_j\psi=U_j\psi\otimes|0\rangle$.
--
--   The inequality of Theorem 1 is thus a family of inequalities, and it is this family that the proof of Theorem 2 uses.
--
--   Differences from the source:
--   - reading: Eq. (1): ρ = ∑ᵢ pᵢ ρᵢ₁ ⊗ ρᵢ₂ with the index range left open → ρ lies in the trace-norm closed convex hull of product states (Holevo–Shirokov–Werner); reason: the paper's own proof of Theorem 2 concludes separability from the continuous mixture (19), and the closed hull contains every finite, countable and integral mixture of product states
--   - encoding: ⟨(Δû)²⟩_ρ for a quadrature û = w·r̂ → the variance in ℝ≥0∞ of the unique probability law on ℝ whose characteristic function is the Weyl trace tr ρ exp(i t w·r̂); reason: this is the variance of the observable; the value is ⊤ when the second moment is infinite, a case the paper does not discuss and in which (3) holds trivially
--   - encoding: the state after LLUBOs U_l, whose correlation matrix changes by the congruence of Eq. (9) → the covariance SᵀVS and the quadratures (S w)·r̂ evaluated on the original ρ, with S = S₁ ⊕ S₂ symplectic; reason: this is the Heisenberg form the paper states on p. 3; the numbers are the same, and a 2 × 2 real matrix is symplectic exactly when its determinant is 1
--   - reading: the operators x̂ⱼ, p̂ⱼ can be any local operators satisfying the commutators; in particular an arbitrary local unitary U₁ ⊗ U₂ → (1) the canonical pairs given by columns of local symplectic matrices, and (2) the pairs Wⱼ†(x̂ⱼ ⊗ I)Wⱼ, Wⱼ†(p̂ⱼ ⊗ I)Wⱼ for every pair of isometries Wⱼ : ℓ²(ℕ) → ℓ²(ℕ × ℕ), i.e. variances in the local-isometry image of ρ; reason: by the Stone–von Neumann theorem every Weyl-regular canonical pair on ℓ²(ℕ) is unitarily a multiple of (x̂, p̂), i.e. of this form, and Wⱼψ = Uⱼψ ⊗ |0⟩ gives the paper's U₁ ⊗ U₂; pairs satisfying the commutator only on a domain without Weyl regularity are excluded because the uncertainty relation the proof uses fails for them (x̂ and −i d/dx with periodic boundary conditions on L²[0,1] have Var p̂ = 0 in an eigenstate)
--   - generalization: the operators of Eq. (2), whose signs are + on x̂₂ and − on p̂₂ → independent signs s, t = ±1 on x̂₂ and p̂₂; reason: the paper's proof uses only Var x̂ⱼ + Var p̂ⱼ ≥ 1 per mode; s = 1, t = −1 is the paper's case
-- source:
--   Duan, Giedke, Cirac, Zoller, Inseparability criterion for continuous variable systems, arXiv:quant-ph/9908056v2, remark after Theorem 1, p. 2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P47
import Definitions.Def_DuanCV_Gauss_IsSeparableTwoMode
import Definitions.Def_DuanCV_Gauss_quadVariance
import Definitions.Def_DuanCV_Gauss_eprU
import Definitions.Def_DuanCV_Gauss_eprV
import Definitions.Def_DuanCV_Gauss_localIsometryImage

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Claimed50.P19 (Cov FockIndex)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Frontier30.P08 (isSymplectic)
open QAlgorithms.Papers.Independent.Gap48.P47 (localSymplecticMatrix)

namespace DuanCV.Gauss

/-- **Theorem 1 for arbitrary local canonical pairs, local unitaries and either sign.**
Duan, Giedke, Cirac, Zoller, *Inseparability criterion for continuous variable systems*, arXiv:quant-ph/9908056v2, remark after Theorem 1, p. 2.

For every separable state, every real `a ≠ 0` and all signs `s, t = ±1`, write
`û = |a|x̂₁ + (s/a)x̂₂`, `v̂ = |a|p̂₁ + (t/a)p̂₂`. The bound (3) holds in two forms: (1) with `(x̂ⱼ, p̂ⱼ)`
replaced by the canonical pair given by the columns of a local symplectic `Sⱼ`, and (2) with
`(x̂ⱼ, p̂ⱼ)` replaced by `(Wⱼ†(x̂ⱼ ⊗ I)Wⱼ, Wⱼ†(p̂ⱼ ⊗ I)Wⱼ)` for arbitrary local isometries
`Wⱼ : ℓ²(ℕ) → ℓ²(ℕ) ⊗ ℓ²(ℕ)`, i.e. the variances are taken in `localIsometryImage W1 W2 ρ`.

**Formalization Note.** In (1) the transformed quadrature is `(S.mulVec w)·r̂`, whose covariance is
`SᵀVS = localCongruence V S1 S2`. In (2), by Stone–von Neumann, every Weyl-regular canonical pair on
the one-mode space is `Wⱼ†(x̂ ⊗ I)Wⱼ, Wⱼ†(p̂ ⊗ I)Wⱼ` for some such isometry onto `ℓ²(ℕ) ⊗ K`, and the
paper's arbitrary local unitary `U₁ ⊗ U₂` is the case `Wⱼ ψ = Uⱼψ ⊗ |0⟩`. The signs `s`, `t` are
independent: the sign pair `s = t` is not a symplectic image of (2), but it is what the 'only if'
part of Theorem 2 needs. -/
theorem theorem_1_local_canonical_pairs (ρ : State (FockIndex 2))
    (hρ : IsSeparableTwoMode ρ.coefficients) (a : ℝ) (ha : a ≠ 0)
    (s t : ℝ) (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1) :
    (∀ S1 S2 : Cov 1, isSymplectic S1 → isSymplectic S2 →
      ENNReal.ofReal (a ^ 2 + 1 / a ^ 2) ≤
        quadVariance ρ.coefficients ((localSymplecticMatrix S1 S2).mulVec (eprU a s)) +
          quadVariance ρ.coefficients ((localSymplecticMatrix S1 S2).mulVec (eprV a t))) ∧
    (∀ W1 W2 : Hilbert ℕ →ₗᵢ[ℂ] Hilbert (ℕ × ℕ),
      ENNReal.ofReal (a ^ 2 + 1 / a ^ 2) ≤
        quadVariance (localIsometryImage W1 W2 ρ.coefficients) (eprU a s) +
          quadVariance (localIsometryImage W1 W2 ρ.coefficients) (eprV a t)) := by sorry

end DuanCV.Gauss
