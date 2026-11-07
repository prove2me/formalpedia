-- Prove2me | Theorems.Thm_DimFreeShadow_lemma_5_3
-- name    : DimFreeShadow.lemma_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:03:25.186667+00:00
-- url     : https://prove2.me/theorems/735cccda-e075-44a2-97c3-264f2292b1b6
-- title:
--   Lemma 5.3 — trace-distance stability under tensor powers
-- statement:
--   If $d_{\mathrm{tr}}(\rho,\sigma)\le s$, then $\|\vartheta(\rho)-\vartheta(\sigma)\|_\infty\le s$, where $\vartheta(\rho)=(\operatorname{Tr}(E_1\rho),\dots,\operatorname{Tr}(E_M\rho))$ for effects $E_1,\dots,E_M$. For every positive integer $T$,
--
--   $$
--   d_{\mathrm{tr}}(\rho^{\otimes T},\sigma^{\otimes T})\le Ts .
--   $$
--
--   So, for every POVM $N$ on $\mathcal H^{\otimes T}$ and every event $A$ in its output alphabet, $|\mathbb P^N_\rho[A]-\mathbb P^N_\sigma[A]|\le Ts$.
--
--   This is the continuity estimate that lifts a guarantee on a finite net of states to all states.
--
--   Differences from the source:
--   - encoding: a finite-dimensional Hilbert space H and its tensor powers → ℂ^d for a finite type d, with H^{⊗T} indexed by Fin T → d; reason: every finite-dimensional Hilbert space is unitarily equivalent to some ℂ^d; the same instances
--   - reading: every POVM N and every event A in its output alphabet, with P^N_ρ[A] defined on p.21 for the finite alphabet Z_ϵ → every POVM with an arbitrary finite outcome type, and every Finset of outcomes; reason: the paper defines P^N only for finite alphabets; this covers every finite alphabet
--   - encoding: ‖ϑ(ρ) − ϑ(σ)‖_∞ ≤ s → |Tr(E_j ρ) − Tr(E_j σ)| ≤ s for each j; reason: the sup norm bound stated coordinatewise, which also covers M = 0
--   - encoding: Tr(·) of an effect times a state (a real number) → the real part .re of the complex trace; reason: the trace of a product of two Hermitian positive semidefinite matrices is real; the same value
-- source:
--   Jeronimo, Huang, Liu, Dimension-Free Polylogarithmic Quantum Shadow Tomography, arXiv:2608.06345 (sha256 a1a42249…), Lemma 5.3, p.23

import Mathlib
import Definitions.Def_ShadowTomography_UpperBound_tensorPow
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_DimFreeShadow_traceDistance

namespace DimFreeShadow

open ShadowTomography.UpperBound (tensorPow)

/-- **Lemma 5.3 (trace-distance stability)** (arXiv:2608.06345, sha256 a1a42249…, Lemma 5.3,
p.23). If `d_tr(ρ, σ) ≤ s`, then `‖ϑ(ρ) − ϑ(σ)‖_∞ ≤ s` (with `ϑ(ρ) = (Tr(E_jρ))_j` for effects
`E_1, …, E_M`) and, for every positive integer `T`, `d_tr(ρ^{⊗T}, σ^{⊗T}) ≤ Ts`. So, for every
POVM `N` on `H^{⊗T}` and every event `A` in its output alphabet, `|P^N_ρ[A] − P^N_σ[A]| ≤ Ts`.

**Formalization Note** `‖·‖_∞ ≤ s` is stated coordinatewise. A POVM has a finite outcome type
`Z` (`QAlgorithms.IsPOVM`) and `P^N_ρ[A] = Σ_{z∈A} Tr(N_z ρ^{⊗T})` (p.21), real parts;
events are `Finset`s of outcomes. -/
theorem lemma_5_3 {d : Type} [Fintype d] [DecidableEq d] (ρ σ : Matrix d d ℂ)
    (hρ : WildeQIT.IsDensityOperator ρ) (hσ : WildeQIT.IsDensityOperator σ) (s : ℝ)
    (hs : traceDistance ρ σ ≤ s) (M : ℕ) (E : Fin M → Matrix d d ℂ)
    (hE : ∀ j, QAlgorithms.IsEffect (E j)) :
    (∀ j, |(E j * ρ).trace.re - (E j * σ).trace.re| ≤ s) ∧
    (∀ T : ℕ, 1 ≤ T → traceDistance (tensorPow ρ T) (tensorPow σ T) ≤ T * s) ∧
    (∀ T : ℕ, 1 ≤ T → ∀ (Z : Type) (_ : Fintype Z) (Nz : Z → Matrix (Fin T → d) (Fin T → d) ℂ),
      QAlgorithms.IsPOVM Nz → ∀ Aev : Finset Z,
        |∑ z ∈ Aev, (Nz z * tensorPow ρ T).trace.re - ∑ z ∈ Aev, (Nz z * tensorPow σ T).trace.re|
          ≤ T * s) := by sorry

end DimFreeShadow
