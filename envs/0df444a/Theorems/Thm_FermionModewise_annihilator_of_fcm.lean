-- Prove2me | Theorems.Thm_FermionModewise_annihilator_of_fcm
-- name    : FermionModewise.annihilator_of_fcm
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:32:06.89859+00:00
-- url     : https://prove2.me/theorems/23bc27f6-8be7-4633-9fd7-ecdac2406f62
-- title:
--   From the FCM to the state (pure case) — annihilators of $\psi$ from the eigenvectors of $M$
-- statement:
--   Let $(\gamma_\alpha)$ be Hermitian operators satisfying the Clifford algebra $\{\gamma_\alpha,\gamma_\beta\}=2\delta_{\alpha\beta}\mathbb 1$, let $\psi$ be a unit vector, and let $M$ be its covariance matrix. Then:
--   1. $\langle\psi,\gamma_\alpha\gamma_\beta\,\psi\rangle=\delta_{\alpha\beta}+i\,M_{\alpha\beta}$ for all $\alpha,\beta$;
--   2. for every complex vector $x$ with $Mx=i\,x$, the operator $\sum_\alpha x_\alpha\gamma_\alpha$ annihilates $\psi$.
--
--   This is the precise content of "the correspondence between FCMs and gaussian states" in the pure case: the covariance matrix determines which linear combinations of quadratures annihilate the state. For the vacuum of one mode, $M=J_2$, $x=\tfrac12(1,-i)$ and $\sum_\alpha x_\alpha\gamma_\alpha=b$.
--
--   Differences from the source:
--   - reading: "the correspondence between FCMs and gaussian mixed states" (invoked, not proved) → (1) the two-point function from the FCM and (2) annihilators of ψ from the eigenvectors of M with eigenvalue i; reason: this is the part of the correspondence that the pure case of the decomposition uses
--   - generalization: Gaussian states and their quadratures → any Hermitian Clifford family and any unit vector; reason: the argument needs only (6) and (8)
-- source:
--   Botero–Reznik, arXiv:quant-ph/0404176v3, p.6 (after (12)); with (6), p.4 and (8), p.5

import Mathlib
import Definitions.Def_FermionModewise_fcm

open Matrix

namespace FermionModewise

/-- **From the FCM to the state, pure case** (Botero–Reznik, arXiv:quant-ph/0404176v3, p.6: "From
the correspondence between FCMs and gaussian mixed states"): let `γ` be a family of Hermitian
operators satisfying the Clifford algebra (6), let `ψ` be a unit vector and `M` its FCM. Then
(a) `⟨ψ, γ_α γ_β ψ⟩ = δ_αβ + i M_αβ`; and (b) for every complex vector `x` with `M x = i x`, the
operator `Σ_α x_α γ_α` annihilates `ψ`.

**Formalization Note.** The page invokes the correspondence without proof; this is the form of it
that the pure case uses: the state is determined through the operators that annihilate it, read
off from the FCM. `M x` uses `M` with real entries embedded in `ℂ`. -/
theorem annihilator_of_fcm {ι ν : Type} [Fintype ι] [DecidableEq ι] [Fintype ν] [DecidableEq ν]
    (γ : ν → Matrix ι ι ℂ) (hherm : ∀ α, (γ α)ᴴ = γ α)
    (hcliff : ∀ α β, γ α * γ β + γ β * γ α = (if α = β then (2 : ℂ) else 0) • (1 : Matrix ι ι ℂ))
    (ψ : ι → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1) :
    (∀ α β, star ψ ⬝ᵥ ((γ α * γ β) *ᵥ ψ) =
        (if α = β then (1 : ℂ) else 0) + Complex.I * (fcm γ ψ α β : ℂ)) ∧
      ∀ x : ν → ℂ, (fcm γ ψ).map (fun r : ℝ => (r : ℂ)) *ᵥ x = Complex.I • x →
        (∑ α, x α • γ α) *ᵥ ψ = 0 := by sorry

end FermionModewise
