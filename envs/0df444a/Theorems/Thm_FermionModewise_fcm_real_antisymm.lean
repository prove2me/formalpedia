-- Prove2me | Theorems.Thm_FermionModewise_fcm_real_antisymm
-- name    : FermionModewise.fcm_real_antisymm
-- status  : Proved
-- author  : @iris
-- created : 2026-11-04T06:32:12.931218+00:00
-- url     : https://prove2.me/theorems/d3a7381b-bd15-4750-bc00-2f632012df0d
-- title:
--   The fermion covariance matrix is real and antisymmetric
-- statement:
--   Let $(\gamma_\alpha)$ be a family of Hermitian operators on a finite-dimensional space. Then:
--   1. for every Hermitian $\rho$ (in particular every density matrix), the numbers
--   $$M_{\alpha\beta}=\frac1{2i}\operatorname{Tr}\big(\rho\,[\gamma_\alpha,\gamma_\beta]\big)$$
--   are real, and $M_{\beta\alpha}=-M_{\alpha\beta}$;
--   2. for every vector $\psi$, the number $\frac1{2i}\langle\psi,[\gamma_\alpha,\gamma_\beta]\psi\rangle$ is real, and the FCM $M$ of $\psi$ satisfies $M^T=-M$.
--
--   So the FCM (8) is a real antisymmetric $2N\times2N$ matrix, which is what allows it to be brought to Williamson form by an orthogonal transformation.
--
--   Differences from the source:
--   - generalization: the FCM of a Gaussian state of the quadratures → any Hermitian family, any Hermitian ρ and any vector ψ; reason: the property uses only Hermiticity, and Gaussian states with their quadratures are an instance
--   - reading: "an antisymmetric 2N × 2N matrix" → real-valued and antisymmetric; reason: realness is implicit, since the next line applies a real orthogonal O to it
-- source:
--   Botero–Reznik, arXiv:quant-ph/0404176v3, eq. (8) and the sentence after it, p.5

import Mathlib
import Definitions.Def_FermionModewise_fcm

open Matrix

namespace FermionModewise

/-- **The FCM is a real antisymmetric matrix** (Botero–Reznik, arXiv:quant-ph/0404176v3, eq. (8),
p.5: "Being an antisymmetric 2N × 2N matrix"): for a family of Hermitian operators `γ`,
(a) for every Hermitian `ρ` (in particular every density matrix), the numbers
`M_αβ = (1/2i) Tr(ρ [γ_α, γ_β])` are real and `M_βα = −M_αβ`; and (b) for every vector `ψ` the
number `(1/2i)⟨ψ, [γ_α, γ_β] ψ⟩` is real and the matrix `fcm γ ψ` is antisymmetric.

**Formalization Note.** Clause (a) covers the mixed states of (8); clause (b) is the pure-state
form used by `fcm`, and shows that the real part taken in `fcm` loses nothing. -/
theorem fcm_real_antisymm {ι ν : Type} [Fintype ι] (γ : ν → Matrix ι ι ℂ)
    (hγ : ∀ α, (γ α)ᴴ = γ α) :
    (∀ ρ : Matrix ι ι ℂ, ρᴴ = ρ → ∀ α β,
      ((1 / (2 * Complex.I)) * Matrix.trace (ρ * (γ α * γ β - γ β * γ α))).im = 0 ∧
      (1 / (2 * Complex.I)) * Matrix.trace (ρ * (γ β * γ α - γ α * γ β)) =
        -((1 / (2 * Complex.I)) * Matrix.trace (ρ * (γ α * γ β - γ β * γ α)))) ∧
    ∀ ψ : ι → ℂ,
      (∀ α β, ((1 / (2 * Complex.I)) * (star ψ ⬝ᵥ ((γ α * γ β - γ β * γ α) *ᵥ ψ))).im = 0) ∧
      (fcm γ ψ)ᵀ = -fcm γ ψ := by sorry

end FermionModewise
