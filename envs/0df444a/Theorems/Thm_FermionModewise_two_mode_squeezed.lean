-- Prove2me | Theorems.Thm_FermionModewise_two_mode_squeezed
-- name    : FermionModewise.two_mode_squeezed
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:32:17.745578+00:00
-- url     : https://prove2.me/theorems/fb0adf0b-99b3-4126-ace7-9ae46876c083
-- title:
--   $T|00\rangle=\cos\theta|00\rangle-\sin\theta|11\rangle$, with FCM (12) at $\lambda=\cos2\theta$, $\kappa=\sin2\theta$
-- statement:
--   Let $a,b$ be two modes satisfying the anticommutation relations, let $|00\rangle$ be a unit vector with $a|00\rangle=b|00\rangle=0$, and let $\theta\in\mathbb R$. Then:
--   1. $T=\exp[-(a^\dagger b^\dagger+ab)\theta]$ is unitary;
--   2. $T|00\rangle=\cos\theta\,|00\rangle-\sin\theta\,|11\rangle$ with $|11\rangle=a^\dagger b^\dagger|00\rangle$, the two-mode squeezed state (3);
--   3. the covariance matrix of this state with respect to the quadratures of $(a,b)$ is the block (12) with $\lambda=\cos2\theta$, $\kappa=\sin2\theta$.
--
--   This identifies the entangled pairs of the normal form (12) at $\lambda_0=1$ with the states (3) of the main result.
--
--   Differences from the source:
--   - generalization: (15) for the parameters of (12) with tan 2θ = κ/λ → every real θ, with λ = cos 2θ and κ = sin 2θ; reason: at λ0 = 1, κ > 0, λ ≥ 0 these coincide for 2θ ∈ (0, π/2], and the cos/sin form is also defined at λ = 0, where tan 2θ = κ/λ is not
--   - generalization: modes on the Fock space → any finite-dimensional representation with a unit joint vacuum; reason: the Fock space is an instance
--   - reading: "T_i|00⟩ which expand out to the form (2)" → T|00⟩ = cos θ|00⟩ − sin θ a†b†|00⟩; reason: (2) is the product of the factors (3), and |11⟩ = a†b†|00⟩ is the convention that gives the minus sign of (3)
-- source:
--   Botero–Reznik, arXiv:quant-ph/0404176v3, eq. (15) and the sentence after it, p.6

import Mathlib
import Definitions.Def_FermionModewise_IsCAR
import Definitions.Def_FermionModewise_majorana
import Definitions.Def_FermionModewise_fcm
import Definitions.Def_FermionModewise_pairBlock
import Definitions.Def_FermionModewise_squeezeFactor
import Definitions.Def_FermionModewise_squeezeT

open Matrix

namespace FermionModewise

/-- **The entangling unitary produces the two-mode squeezed state (3)** (Botero–Reznik,
arXiv:quant-ph/0404176v3, eq. (15) and the sentence after it, p.6): for two modes `a, b` satisfying
the anticommutation relations and a unit joint vacuum `|00⟩` (`a|00⟩ = b|00⟩ = 0`),
`T = exp[−(a†b† + ab)θ]` is unitary, `T|00⟩ = cos θ |00⟩ − sin θ a†b†|00⟩`, and the FCM of `T|00⟩`
on the quadratures of `(a, b)` is the block (12) with `λ = cos 2θ`, `κ = sin 2θ`.

**Formalization Note.** (15) prints `tan 2θ = κ/λ`, undefined at `λ = 0`; the statement uses
`λ = cos 2θ`, `κ = sin 2θ`, which is what (15) means for `λ₀ = 1` and is defined everywhere. The
convention `|11⟩ = a†b†|00⟩` gives the minus sign of (3). -/
theorem two_mode_squeezed {ι : Type} [Fintype ι] [DecidableEq ι] (a b : Matrix ι ι ℂ)
    (hab : IsCAR ![a, b]) (vac : ι → ℂ) (hvac : star vac ⬝ᵥ vac = 1)
    (ha : a *ᵥ vac = 0) (hb : b *ᵥ vac = 0) (θ : ℝ) :
    squeezeT a b θ ∈ Matrix.unitaryGroup ι ℂ ∧
      squeezeT a b θ *ᵥ vac = squeezeFactor a b θ *ᵥ vac ∧
      fcm (majorana ![a, b]) (squeezeFactor a b θ *ᵥ vac) =
        pairBlock (Real.cos (2 * θ)) (Real.sin (2 * θ)) := by sorry

end FermionModewise
