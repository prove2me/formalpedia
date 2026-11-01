-- Prove2me | Theorems.Thm_AccessibleMaps_proposition_1
-- name    : AccessibleMaps.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T16:08:36.439406+00:00
-- url     : https://prove2.me/theorems/6a8c83fa-39f8-4b73-8856-36b1b8435eaf
-- title:
--   Proposition 1: an affinely accessible map is a trace-preserving CP map plus a traceless term at most quadratic in $\rho$
-- statement:
--   Let $\mathcal H$ be a complex Hilbert space, $E_{\mathcal V}(\rho)=g+G\rho$ an affine assignment on an admissible domain $\mathcal V$ of states of $\mathbb C^{a}$, and $U$ a unitary on $\mathbb C^{a}\otimes\mathcal H$, so that
--   $$
--   \Phi(\rho)=\operatorname{tr}_B\big[U\,E_{\mathcal V}(\rho)\,U^\dagger\big]
--   $$
--   is affinely accessible. Put $\omega(\rho)=\operatorname{tr}_A E_{\mathcal V}(\rho)$, $\Lambda_\rho(\sigma)=\operatorname{tr}_B[U(\sigma\otimes\omega(\rho))U^\dagger]$, $C(\rho)=E_{\mathcal V}(\rho)-\rho\otimes\omega(\rho)$, $X(\rho)=\operatorname{tr}_B[U\,C(\rho)\,U^\dagger]$, $b=\operatorname{tr}_A g$ and $B=\operatorname{tr}_A\circ G$. Then:
--
--   1. **Trace-preserving CP.** For every $\rho\in\mathcal V$ there are finitely many matrices $M_k$ with $\Lambda_\rho(\sigma)=\sum_k M_k\sigma M_k^\dagger$ for every matrix $\sigma$ and $\sum_k M_k^\dagger M_k=\mathbb 1$.
--   2. **At most linear dependence on $\rho$.** There are a map $\Lambda^0$ and a real-linear $\Lambda^1$ with $\Lambda_\rho=\Lambda^0+\Lambda^1\rho$ for every $\rho\in\mathcal V$.
--   3. **Traceless.** For every $\rho\in\mathcal V$, $X(\rho)$ is Hermitian and $\operatorname{tr}X(\rho)=0$.
--   4. **At most quadratic, as in (25).** For every $\rho\in\mathcal V$, $C(\rho)=g+G\rho-\rho\otimes b-\rho\otimes B\rho$; and there are $X^0$, a real-linear $X^1$ and a real-bilinear $X^2$ with $X(\rho)=X^0+X^1\rho+X^2(\rho,\rho)$ for every $\rho\in\mathcal V$.
--   5. **Affine form (23).** For every $\rho\in\mathcal V$,
--   $$
--   \Phi(\rho)=\Lambda_\rho(\rho)+X(\rho).
--   $$
--   6. **Linear case (16).** If $\omega$ and $C$ are constant on $\mathcal V$, then for a fixed $\rho_1\in\mathcal V$ every $\rho\in\mathcal V$ has $\Phi(\rho)=\Lambda_{\rho_1}(\rho)+X(\rho_1)$.
--
--   The paper states this as a necessary condition for accessibility: a map with no such affine form, such as the transposition of a qubit, is not accessible through a linear extension.
--
--   The splitting is the one built in the proof: $\Lambda_\rho$ and $X$ are the named objects above, not arbitrary maps. A bare existence statement would be empty, since $\Lambda=\mathrm{id}$ and $X=\Phi-\mathrm{id}$ work for any trace-preserving Hermiticity-preserving map, transposition included.
--
--   Differences from the source:
--   - reading: "the existence of the affine form as in Eq. (16) with a trace-preserving completely positive map … and a traceless inhomogeneous part" → the affine form with the specific Λ_ρ and X(ρ) built from U and E_V, clauses 1–6; reason: a bare existential is satisfied by Λ = id for every trace-preserving map, against the paper's remark (p.5) that transposition has no affine form
--   - reading: "linearly accessible" / "accessible through a linear extension" → affinely accessible (Definition, p.4): an affine assignment (21) and a fixed unitary; reason: §IV and Eq. (25) use the B_jk, G_ijk of Eq. (21); the linear case (13) is the special case of constant ω
--   - generalization: finite-dimensional systems (p.1), with the infinite-dimensional ancilla treated only in the proof of Proposition 1 → the ancilla H is any complex Hilbert space, with no finite dimension or separability; reason: the proof of Proposition 1 treats the infinite-dimensional case; finite-dimensional H is a special case
--   - generalization: the domain V is a finite-volume subset of M_A (p.2) → V is a nonempty set of density matrices whose differences span all traceless Hermitian matrices (its convex hull has positive volume); reason: p.2 asks that convex combinations of the states span a finite-volume region; every positive-volume V satisfies the Lean condition
--   - generalization: Kraus operators M_μν indexed by pairs μν (infinite when H is infinite-dimensional) → a finite Kraus family, valid for every matrix σ; reason: a finite family is a countable one (pad with zeros); the system is finite-dimensional
--   - encoding: Fano coefficients α, β, γ, Γ and SU(d) generators σ_i^A, σ_j^B → coordinate-free operators on the block space C^a ⊗ H (PiLp 2), with tr_A, tr_B blockwise; reason: generators have no finite form for infinite-dimensional H; the operator form has the same instances
--   - encoding: Eq. (13) with g_ij a constant matrix (the linear case of clause 6) → ω(ρ) and C(ρ) constant on V; reason: constant β is constant ω, and then Γ_ij = g_ij/(d_A d_B) is constant, i.e. C is constant; the converse also holds
-- source:
--   Carteret, Terno & Życzkowski, Dynamics beyond completely positive maps, arXiv:quant-ph/0512167v3, Proposition 1, p.5

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_AccessibleMaps_accessibleMap
import Definitions.Def_AccessibleMaps_dilationMap
import Definitions.Def_AccessibleMaps_inhomogeneousPart

open PeresTerno

namespace AccessibleMaps

variable {a H : Type*} [Fintype a] [DecidableEq a] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- **Proposition 1.** Let `Φ(ρ) = tr_B [U E_𝒱(ρ) U†]` be affinely accessible, with `E_𝒱(ρ) = g + G ρ`,
`ω(ρ) = tr_A E_𝒱(ρ)`, `Λ_ρ(σ) = tr_B [U (σ ⊗ ω(ρ)) U†]`, `C(ρ) = E_𝒱(ρ) - ρ ⊗ ω(ρ)` and
`X(ρ) = tr_B [U C(ρ) U†]`. Then:

1. for `ρ ∈ 𝒱`, `Λ_ρ` is a trace-preserving completely positive map, in finite Kraus form on all
   matrices;
2. `ρ ↦ Λ_ρ` is at most linear on `𝒱`;
3. for `ρ ∈ 𝒱`, `X(ρ)` is Hermitian and traceless;
4. `C(ρ) = g + G ρ - ρ ⊗ b - ρ ⊗ B ρ` for `ρ ∈ 𝒱`, with `b = tr_A g`, `B = tr_A ∘ G`, and `X` is at
   most quadratic on `𝒱`, as in Eq. (25);
5. `Φ(ρ) = Λ_ρ(ρ) + X(ρ)` for `ρ ∈ 𝒱`, the affine form of Eq. (23);
6. if `ω` and `C` are constant on `𝒱`, then `Φ(ρ) = Λ_{ρ₁}(ρ) + X(ρ₁)` for fixed `ρ₁ ∈ 𝒱` and every
   `ρ ∈ 𝒱`, the state-independent affine form of Eq. (16).

Carteret, Terno & Życzkowski, arXiv:quant-ph/0512167v3, Proposition 1, p.5 (PDF p.5).

**Formalization Note.** The splitting is the one the proof builds: `Λ_ρ` and `X` are the named
objects, never existentially chosen, because a bare "there exist `Λ` and `X`" is empty (`Λ = id`,
`X = Φ - id`). "Accessible through a linear extension" is read as affinely accessible (Definition,
p.4, PDF p.4), because Eq. (25) needs the coefficients of Eq. (21). `H` is any complex Hilbert space. -/
theorem proposition_1 (E : AffineAssignment a H)
    (U : unitary (Composite a H →L[ℂ] Composite a H)) :
    (∀ ρ ∈ E.V, ∃ (N : ℕ) (M : Fin N → Matrix a a ℂ),
      (∀ σ : Matrix a a ℂ, dilationMap E U ρ σ = krausUpdate M σ) ∧ povmElement M = 1) ∧
    (∃ (Λ₀ : Matrix a a ℂ → Matrix a a ℂ)
      (Λ₁ : Matrix a a ℂ →ₗ[ℝ] (Matrix a a ℂ → Matrix a a ℂ)),
      ∀ ρ ∈ E.V, dilationMap E U ρ = Λ₀ + Λ₁ ρ) ∧
    (∀ ρ ∈ E.V, (inhomogeneousPart E U ρ).IsHermitian ∧ (inhomogeneousPart E U ρ).trace = 0) ∧
    (∀ ρ ∈ E.V, E.correlation ρ =
      E.g + E.G ρ - tensorOp ρ (trA E.g) - tensorOp ρ (trA (E.G ρ))) ∧
    (∃ (X₀ : Matrix a a ℂ) (X₁ : Matrix a a ℂ →ₗ[ℝ] Matrix a a ℂ)
      (X₂ : Matrix a a ℂ →ₗ[ℝ] Matrix a a ℂ →ₗ[ℝ] Matrix a a ℂ),
      ∀ ρ ∈ E.V, inhomogeneousPart E U ρ = X₀ + X₁ ρ + X₂ ρ ρ) ∧
    (∀ ρ ∈ E.V, accessibleMap E U ρ = dilationMap E U ρ ρ + inhomogeneousPart E U ρ) ∧
    ((∀ ρ ∈ E.V, ∀ ρ' ∈ E.V, E.marginal ρ = E.marginal ρ') →
      (∀ ρ ∈ E.V, ∀ ρ' ∈ E.V, E.correlation ρ = E.correlation ρ') →
      ∀ ρ₁ ∈ E.V, ∀ ρ ∈ E.V,
        accessibleMap E U ρ = dilationMap E U ρ₁ ρ + inhomogeneousPart E U ρ₁) := by sorry

end AccessibleMaps
