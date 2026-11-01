-- Prove2me | Theorems.Thm_AccessibleMaps_eq_16
-- name    : AccessibleMaps.eq_16
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T16:08:41.541561+00:00
-- url     : https://prove2.me/theorems/12b53ff1-aaf6-42ed-88f0-41d7141e419c
-- title:
--   Eq. (16): the state-independent affine form in the linear case
-- statement:
--   Let $E_{\mathcal V}$ be an affine assignment on an admissible domain $\mathcal V$ and $U$ a unitary on $\mathbb C^{a}\otimes\mathcal H$. Suppose the environment marginal $\omega(\rho)$ and the correlation term $C(\rho)$ are the same for all $\rho\in\mathcal V$ (the linear case, Eq. (13), with a constant matrix $g_{ij}$). Then for any fixed $\rho_1\in\mathcal V$ and every $\rho\in\mathcal V$,
--   $$
--   \Phi(\rho)=\Lambda_{\rho_1}(\rho)+X(\rho_1),
--   $$
--   where $\Lambda_{\rho_1}(\sigma)=\operatorname{tr}_B[U(\sigma\otimes\omega(\rho_1))U^\dagger]$ is a fixed trace-preserving CP map (see Eq. (15)) and $X(\rho_1)=\operatorname{tr}_B[U\,C(\rho_1)\,U^\dagger]$ a fixed traceless matrix. This is the paper's affine form (16), in which neither the Kraus operators nor the inhomogeneous term depends on $\rho$.
--
--   Differences from the source:
--   - generalization: finite-dimensional systems (p.1), with the infinite-dimensional ancilla treated only in the proof of Proposition 1 → the ancilla H is any complex Hilbert space, with no finite dimension or separability; reason: the proof of Proposition 1 treats the infinite-dimensional case; finite-dimensional H is a special case
--   - generalization: the domain V is a finite-volume subset of M_A (p.2) → V is a nonempty set of density matrices whose differences span all traceless Hermitian matrices (its convex hull has positive volume); reason: p.2 asks that convex combinations of the states span a finite-volume region; every positive-volume V satisfies the Lean condition
--   - encoding: Eq. (13): β_j = b_j and γ_ij = g_ij + α_i b_j with g_ij a constant matrix → ω(ρ) and C(ρ) constant on V; reason: constant β is constant ω, and then Γ_ij = g_ij/(d_A d_B) is constant, i.e. C is constant; the converse also holds
--   - encoding: Fano coefficients α, β, γ, Γ and SU(d) generators σ_i^A, σ_j^B → coordinate-free operators on the block space C^a ⊗ H (PiLp 2), with tr_A, tr_B blockwise; reason: generators have no finite form for infinite-dimensional H; the operator form has the same instances
-- source:
--   Carteret, Terno & Życzkowski, Dynamics beyond completely positive maps, arXiv:quant-ph/0512167v3, Eq. (16), p.3, with the linear case Eq. (13), p.3

import Mathlib
import Definitions.Def_AccessibleMaps_accessibleMap
import Definitions.Def_AccessibleMaps_dilationMap
import Definitions.Def_AccessibleMaps_inhomogeneousPart

namespace AccessibleMaps

variable {a H : Type*} [Fintype a] [DecidableEq a] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The state-independent affine form in the linear case: if the marginal `ω` and the correlation
term `C` are constant on `𝒱`, then for any fixed `ρ₁ ∈ 𝒱`, every `ρ ∈ 𝒱` has `Φ(ρ) = Λ_{ρ₁}(ρ) + X(ρ₁)`.

Carteret, Terno & Życzkowski, arXiv:quant-ph/0512167v3, Eq. (16), p.3 (PDF p.3), with the linear case
Eq. (13), p.3 (PDF p.3), for a constant matrix `g_ij`.

**Formalization Note.** Eq. (13) with constant `g_ij` says exactly that `ω` is constant and the
correlation tensor `Γ_ij = g_ij/(d_A d_B)` is constant. The operator form replaces the generators. -/
theorem eq_16 (E : AffineAssignment a H) (U : unitary (Composite a H →L[ℂ] Composite a H))
    (hω : ∀ ρ ∈ E.V, ∀ ρ' ∈ E.V, E.marginal ρ = E.marginal ρ')
    (hC : ∀ ρ ∈ E.V, ∀ ρ' ∈ E.V, E.correlation ρ = E.correlation ρ')
    (ρ₁ : Matrix a a ℂ) (hρ₁ : ρ₁ ∈ E.V) (ρ : Matrix a a ℂ) (hρ : ρ ∈ E.V) :
    accessibleMap E U ρ = dilationMap E U ρ₁ ρ + inhomogeneousPart E U ρ₁ := by sorry

end AccessibleMaps
