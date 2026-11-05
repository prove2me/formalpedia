-- Prove2me | Theorems.Thm_FermionModewise_pure_fcm_sq
-- name    : FermionModewise.pure_fcm_sq
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:34:00.493491+00:00
-- url     : https://prove2.me/theorems/6af0d3e4-2b19-49e2-9dfe-dc7dc17fc023
-- title:
--   Pure Gaussian states satisfy $-M^2=\mathbb 1$
-- statement:
--   Let $(b_k)$ satisfy the anticommutation relations on a finite-dimensional space, and let $\psi$ be a pure fermion Gaussian state of these modes. Then its covariance matrix $M$ (with respect to the quadratures of $b$) satisfies
--   $$-M^2=\mathbb 1 .$$
--
--   This is the characterization of purity in terms of the FCM. In the proof of the main result it makes the global covariance matrix isotropic with $\lambda_0=1$, so that the normal form (11)–(12) applies.
--
--   Differences from the source:
--   - generalization: Fock space → any finite-dimensional representation of the anticommutation relations; reason: the Fock space is an instance
--   - generalization: pure state of the form (4), ρ = ⊗ρ̃_k with |λ_k| = 1 → each factor ρ̃_k fixes ψ (IsPureGaussian); reason: implied by ρ = |ψ⟩⟨ψ| = ∏ρ̃_k, and equivalent to it in the Fock representation
-- source:
--   Botero–Reznik, arXiv:quant-ph/0404176v3, p.5 (before (10))

import Mathlib
import Definitions.Def_FermionModewise_IsPureGaussian
import Definitions.Def_FermionModewise_majorana
import Definitions.Def_FermionModewise_fcm

open Matrix

namespace FermionModewise

/-- **Purity criterion** (Botero–Reznik, arXiv:quant-ph/0404176v3, p.5): the FCM `M` of a pure
fermion Gaussian state satisfies `−M² = 1`.

**Formalization Note.** Stated for any finite representation of the anticommutation relations
and any pure Gaussian state in the sense of `IsPureGaussian` (both signs of `λ_k`). -/
theorem pure_fcm_sq {ι μ : Type} [Fintype ι] [DecidableEq ι] [Fintype μ] [DecidableEq μ]
    (b : μ → Matrix ι ι ℂ) (hb : IsCAR b) (ψ : ι → ℂ) (hψ : IsPureGaussian b ψ) :
    fcm (majorana b) ψ * fcm (majorana b) ψ = -1 := by sorry

end FermionModewise
