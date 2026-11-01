-- Prove2me | Theorems.Thm_AccessibleMaps_inhomogeneous_traceless
-- name    : AccessibleMaps.inhomogeneous_traceless
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T16:08:31.181263+00:00
-- url     : https://prove2.me/theorems/da23c5bf-a0be-42e5-93d2-1728a691ff2d
-- title:
--   The inhomogeneous part $X(\rho)$ is Hermitian and traceless
-- statement:
--   Let $E_{\mathcal V}(\rho)=g+G\rho$ be an affine assignment on an admissible domain $\mathcal V$, with environment marginal $\omega(\rho)=\operatorname{tr}_A E_{\mathcal V}(\rho)$ and correlation term $C(\rho)=E_{\mathcal V}(\rho)-\rho\otimes\omega(\rho)$, and let $U$ be a unitary on $\mathbb C^{a}\otimes\mathcal H$. Then for every $\rho\in\mathcal V$ the inhomogeneous part
--   $$
--   X(\rho)=\operatorname{tr}_B\big[U\,C(\rho)\,U^\dagger\big]
--   $$
--   is a Hermitian matrix with $\operatorname{tr}X(\rho)=0$.
--
--   In the paper's coordinates, $X(\rho)=\vec\xi\cdot\vec\sigma^A$ with real coefficients $\xi_i$: tracelessness is what lets it be written in the generators, and Hermiticity is the reality of $\vec\xi$.
--
--   Differences from the source:
--   - generalization: finite-dimensional systems (p.1), with the infinite-dimensional ancilla treated only in the proof of Proposition 1 → the ancilla H is any complex Hilbert space, with no finite dimension or separability; reason: the proof of Proposition 1 treats the infinite-dimensional case; finite-dimensional H is a special case
--   - generalization: the domain V is a finite-volume subset of M_A (p.2) → V is a nonempty set of density matrices whose differences span all traceless Hermitian matrices (its convex hull has positive volume); reason: p.2 asks that convex combinations of the states span a finite-volume region; every positive-volume V satisfies the Lean condition
--   - reading: "linearly accessible" / "accessible through a linear extension" → affinely accessible (Definition, p.4): an affine assignment (21) and a fixed unitary; reason: §IV and Eq. (25) use the B_jk, G_ijk of Eq. (21); the linear case (13) is the special case of constant ω
--   - encoding: X = ξ·σ^A with real ξ → X(ρ) is Hermitian with trace 0; reason: a matrix is a real combination of the traceless Hermitian generators exactly when it is Hermitian and traceless
--   - encoding: Fano coefficients α, β, γ, Γ and SU(d) generators σ_i^A, σ_j^B → coordinate-free operators on the block space C^a ⊗ H (PiLp 2), with tr_A, tr_B blockwise; reason: generators have no finite form for infinite-dimensional H; the operator form has the same instances
-- source:
--   Carteret, Terno & Życzkowski, Dynamics beyond completely positive maps, arXiv:quant-ph/0512167v3, §IV, p.4 ("the inhomogeneous part is traceless"; "all the coefficients ξ_i are real") and the proof of Proposition 1, p.5

import Mathlib
import Definitions.Def_AccessibleMaps_inhomogeneousPart

namespace AccessibleMaps

variable {a H : Type*} [Fintype a] [DecidableEq a] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- For `ρ ∈ 𝒱`, the inhomogeneous part `X(ρ) = tr_B [U C(ρ) U†]` is Hermitian and traceless.

Carteret, Terno & Życzkowski, arXiv:quant-ph/0512167v3, §IV, p.4 (PDF p.4), and the proof of Proposition 1,
p.5 (PDF p.5).

**Formalization Note.** `C(ρ)` is a difference of two trace-class operators, so `X(ρ)` is not a junk
value of `basisOperatorTrace`. -/
theorem inhomogeneous_traceless (E : AffineAssignment a H)
    (U : unitary (Composite a H →L[ℂ] Composite a H)) (ρ : Matrix a a ℂ) (hρ : ρ ∈ E.V) :
    (inhomogeneousPart E U ρ).IsHermitian ∧ (inhomogeneousPart E U ρ).trace = 0 := by sorry

end AccessibleMaps
