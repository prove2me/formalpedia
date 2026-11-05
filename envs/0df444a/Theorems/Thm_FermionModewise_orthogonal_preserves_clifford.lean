-- Prove2me | Theorems.Thm_FermionModewise_orthogonal_preserves_clifford
-- name    : FermionModewise.orthogonal_preserves_clifford
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:33:02.059809+00:00
-- url     : https://prove2.me/theorems/823cfd73-4c4e-4779-aea3-3d4ac13d19df
-- title:
--   $O(2N)$ preserves the Clifford algebra and acts on the FCM by $M\mapsto OMO^T$
-- statement:
--   Let $(b_i)_{i\in\mu}$ satisfy the anticommutation relations, with quadratures $\gamma$, and let $O$ be a real orthogonal matrix on the quadrature index ($O\in O(2N)$, $N=|\mu|$, improper $O$ included). Put
--   $$\tilde\gamma_\alpha=\sum_\beta O_{\alpha\beta}\,\gamma_\beta,\qquad c_i=\tfrac12\big(\tilde\gamma_{(i,0)}-i\,\tilde\gamma_{(i,1)}\big).$$
--   Then:
--   1. every $\tilde\gamma_\alpha$ is Hermitian and $\{\tilde\gamma_\alpha,\tilde\gamma_\beta\}=2\delta_{\alpha\beta}\mathbb 1$;
--   2. $(c_i)$ is a canonical family obtained from $b$, and its quadratures are exactly the $\tilde\gamma_\alpha$;
--   3. for every vector $\psi$, the covariance matrices are related by $\widetilde M=O\,M\,O^T$, where $M$ and $\widetilde M$ are the FCMs of $\psi$ with respect to $\gamma$ and $\tilde\gamma$.
--
--   This is the statement that $O(2N)$ is the group of fermion canonical transformations, used on p.5 to bring an FCM to Williamson form and on p.6 to apply local transformations $O_A\oplus O_B$.
--
--   Differences from the source:
--   - reading: "preserves the Clifford algebra (6) and hence the anticommutation algebra" → the rotated quadratures satisfy (6), the modes built from them form a canonical family with those quadratures, and the FCM transforms as OMOᵀ; reason: this is how p.5 uses the statement ("the gaussian state ρ then takes the form (4) with W as its FCM")
--   - generalization: modes on the Fock space, covariance of Gaussian states → any finite-dimensional representation, covariance law for every vector; reason: the identities are algebraic, and Gaussian states on the Fock space are an instance
-- source:
--   Botero–Reznik, arXiv:quant-ph/0404176v3, p.4 (after (6)); p.5 (after (9))

import Mathlib
import Definitions.Def_FermionModewise_IsCanonicalFamily
import Definitions.Def_FermionModewise_majorana
import Definitions.Def_FermionModewise_fcm

open Matrix

namespace FermionModewise

/-- **`O(2N)` acts by canonical transformations** (Botero–Reznik, arXiv:quant-ph/0404176v3, p.4,
and p.5 after (9)): for modes `b` satisfying the anticommutation relations and a real orthogonal
`O` on the quadrature index, the rotated quadratures `γ̃_α = Σ_β O_αβ γ_β` are Hermitian and satisfy
the Clifford algebra (6); the modes `c_i = ½(γ̃_(i,0) − i γ̃_(i,1))` built from them form a canonical
family obtained from `b`, whose quadratures are exactly `γ̃`; and the FCM transforms as
`M̃ = O M Oᵀ` in every state `ψ`.

**Formalization Note.** `O ∈ O(2N)` is `O ∈ Matrix.orthogonalGroup (μ × Fin 2) ℝ`, improper `O`
included. The covariance law holds for every vector `ψ`. -/
theorem orthogonal_preserves_clifford {ι μ : Type} [Fintype ι] [DecidableEq ι] [Fintype μ]
    [DecidableEq μ] (b : μ → Matrix ι ι ℂ) (hb : IsCAR b)
    (O : Matrix (μ × Fin 2) (μ × Fin 2) ℝ) (hO : O ∈ Matrix.orthogonalGroup (μ × Fin 2) ℝ)
    (ψ : ι → ℂ) :
    let γt : μ × Fin 2 → Matrix ι ι ℂ := fun p => ∑ q, ((O p q : ℝ) : ℂ) • majorana b q
    let c : μ → Matrix ι ι ℂ := fun i => (1 / 2 : ℂ) • (γt (i, 0) - Complex.I • γt (i, 1))
    (∀ p, (γt p)ᴴ = γt p) ∧
      (∀ p q, γt p * γt q + γt q * γt p = (if p = q then (2 : ℂ) else 0) • (1 : Matrix ι ι ℂ)) ∧
      IsCanonicalFamily b c ∧ majorana c = γt ∧
      fcm γt ψ = O * fcm (majorana b) ψ * Oᵀ := by sorry

end FermionModewise
