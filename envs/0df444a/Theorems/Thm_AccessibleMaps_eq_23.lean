-- Prove2me | Theorems.Thm_AccessibleMaps_eq_23
-- name    : AccessibleMaps.eq_23
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T16:08:51.906708+00:00
-- url     : https://prove2.me/theorems/922c8a91-cc05-4d47-b7cc-c6b672ce250b
-- title:
--   Eq. (23): the affine form $\Phi(\rho)=\Lambda_\rho(\rho)+X(\rho)$
-- statement:
--   Let $E_{\mathcal V}$ be an affine assignment on an admissible domain $\mathcal V$, $U$ a unitary on $\mathbb C^{a}\otimes\mathcal H$, and $\Phi(\rho)=\operatorname{tr}_B[U E_{\mathcal V}(\rho)U^\dagger]$ the affinely accessible map. With $\Lambda_\rho(\sigma)=\operatorname{tr}_B[U(\sigma\otimes\omega(\rho))U^\dagger]$ and $X(\rho)=\operatorname{tr}_B[U\,C(\rho)\,U^\dagger]$, every $\rho\in\mathcal V$ satisfies
--   $$
--   \Phi(\rho)=\Lambda_\rho(\rho)+X(\rho).
--   $$
--   This is the paper's affine form (23): the Kraus sum $\sum_a M_a\rho M_a^\dagger$ is $\Lambda_\rho(\rho)$ (Eq. (15)), and the sum $\sum_\mu\sum_{i,j}\Gamma_{ij}\langle\mu|U\sigma^A_i\otimes\sigma^B_jU^\dagger|\mu\rangle$ is $X(\rho)$.
--
--   Differences from the source:
--   - generalization: finite-dimensional systems (p.1), with the infinite-dimensional ancilla treated only in the proof of Proposition 1 → the ancilla H is any complex Hilbert space, with no finite dimension or separability; reason: the proof of Proposition 1 treats the infinite-dimensional case; finite-dimensional H is a special case
--   - generalization: the domain V is a finite-volume subset of M_A (p.2) → V is a nonempty set of density matrices whose differences span all traceless Hermitian matrices (its convex hull has positive volume); reason: p.2 asks that convex combinations of the states span a finite-volume region; every positive-volume V satisfies the Lean condition
--   - reading: "linearly accessible" / "accessible through a linear extension" → affinely accessible (Definition, p.4): an affine assignment (21) and a fixed unitary; reason: §IV and Eq. (25) use the B_jk, G_ijk of Eq. (21); the linear case (13) is the special case of constant ω
--   - encoding: Fano coefficients α, β, γ, Γ and SU(d) generators σ_i^A, σ_j^B → coordinate-free operators on the block space C^a ⊗ H (PiLp 2), with tr_A, tr_B blockwise; reason: generators have no finite form for infinite-dimensional H; the operator form has the same instances
--   - encoding: the Kraus sum Σ_a M_a ρ M_a† of (23) → the named map Λ_ρ(ρ) = tr_B[U(ρ ⊗ ω(ρ))U†]; reason: the M_a are the Kraus operators of Eq. (15), so the sum is this matrix; their existence is the milestone dilation_kraus
-- source:
--   Carteret, Terno & Życzkowski, Dynamics beyond completely positive maps, arXiv:quant-ph/0512167v3, Eq. (23), p.4

import Mathlib
import Definitions.Def_AccessibleMaps_accessibleMap
import Definitions.Def_AccessibleMaps_dilationMap
import Definitions.Def_AccessibleMaps_inhomogeneousPart

namespace AccessibleMaps

variable {a H : Type*} [Fintype a] [DecidableEq a] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The affine form of an affinely accessible map: `Φ(ρ) = Λ_ρ(ρ) + X(ρ)` for `ρ ∈ 𝒱`.

Carteret, Terno & Życzkowski, arXiv:quant-ph/0512167v3, Eq. (23), p.4 (PDF p.4).

**Formalization Note.** The Kraus sum of (23) is `Λ_ρ(ρ)`, see `dilation_kraus`; the second sum is
`X(ρ)`, in operator form with no generators, since those have no finite form for
infinite-dimensional `H`. -/
theorem eq_23 (E : AffineAssignment a H) (U : unitary (Composite a H →L[ℂ] Composite a H))
    (ρ : Matrix a a ℂ) (hρ : ρ ∈ E.V) :
    accessibleMap E U ρ = dilationMap E U ρ ρ + inhomogeneousPart E U ρ := by sorry

end AccessibleMaps
