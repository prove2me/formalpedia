-- Prove2me | Theorems.Thm_AccessibleMaps_eq_25
-- name    : AccessibleMaps.eq_25
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T16:08:59.616452+00:00
-- url     : https://prove2.me/theorems/e46ce806-f41c-49c6-9f8e-91bef3562d1f
-- title:
--   Eq. (25): the correlation term is at most quadratic in $\rho$
-- statement:
--   Let $E_{\mathcal V}(\rho)=g+G\rho$ be an affine assignment on an admissible domain $\mathcal V$ and $U$ a unitary on $\mathbb C^{a}\otimes\mathcal H$. Put $b=\operatorname{tr}_A g$ and $B=\operatorname{tr}_A\circ G$. Then
--
--   1. for every $a\times a$ matrix $\rho$ the correlation term is
--   $$
--   C(\rho)=g+G\rho-\rho\otimes b-\rho\otimes B\rho ,
--   $$
--   2. there are a matrix $X^0$, a real-linear map $X^1$ and a real-bilinear map $X^2$ on $a\times a$ matrices such that the inhomogeneous part satisfies
--   $$
--   X(\rho)=\operatorname{tr}_B\big[U\,C(\rho)\,U^\dagger\big]=X^0+X^1\rho+X^2(\rho,\rho)\qquad\text{for every }\rho\in\mathcal V .
--   $$
--
--   Part 1 is the operator form of the paper's coefficient formula $\Gamma_{ij}=\frac{1}{d_Ad_B}\big(g_{ij}+\sum_k(G_{ijk}-\delta_{ik}b_j)\alpha_k-\sum_kB_{jk}\alpha_i\alpha_k\big)$: the correlation tensor of a general affine assignment depends at most quadratically on $\rho$. Part 2 is the form in which Proposition 1 uses it.
--
--   Differences from the source:
--   - generalization: finite-dimensional systems (p.1), with the infinite-dimensional ancilla treated only in the proof of Proposition 1 → the ancilla H is any complex Hilbert space, with no finite dimension or separability; reason: the proof of Proposition 1 treats the infinite-dimensional case; finite-dimensional H is a special case
--   - generalization: the domain V is a finite-volume subset of M_A (p.2) → V is a nonempty set of density matrices whose differences span all traceless Hermitian matrices (its convex hull has positive volume); reason: p.2 asks that convex combinations of the states span a finite-volume region; every positive-volume V satisfies the Lean condition
--   - reading: "a general assignment map of our example above, in Eq. (26)" → the general affine assignment of Eq. (21); reason: Eq. (26) is a specific qubit assignment with no B_jk or G_ijk; (25) is written in the coefficients of Eq. (21)
--   - encoding: the coefficient formula (25) for Γ_ij with prefactor 1/(d_A d_B) → C(ρ) = g + Gρ − ρ⊗b − ρ⊗Bρ as an operator identity, b = tr_A g, B = tr_A ∘ G; reason: Γ_ij are the generator coefficients of C(ρ); the normalization is absorbed in g, G
--   - generalization: the identity for states ρ of the domain → part 1 for every a × a matrix ρ; reason: the identity is algebraic; states of the domain are a special case
--   - generalization: Γ_ij quadratic in α → additionally, X(ρ) is at most quadratic on V (part 2); reason: part 2 is the consequence Proposition 1 states; dropping it gives the source's claim
-- source:
--   Carteret, Terno & Życzkowski, Dynamics beyond completely positive maps, arXiv:quant-ph/0512167v3, Eq. (25), p.4

import Mathlib
import Definitions.Def_AccessibleMaps_inhomogeneousPart

namespace AccessibleMaps

variable {a H : Type*} [Fintype a] [DecidableEq a] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The correlation term of an affine assignment is at most quadratic in `ρ`: with `b = tr_A g` and
`B = tr_A ∘ G`, one has `C(ρ) = g + G ρ - ρ ⊗ b - ρ ⊗ B ρ`, and on `𝒱` the inhomogeneous part has the
form `X(ρ) = X⁰ + X¹ ρ + X² ρ ρ` with `X¹` real-linear and `X²` real-bilinear.

Carteret, Terno & Życzkowski, arXiv:quant-ph/0512167v3, Eq. (25), p.4 (PDF p.4). The sentence introducing (25)
says "in Eq. (26)"; the general assignment it describes is Eq. (21).

**Formalization Note.** The first identity is the operator form of (25) and holds for every matrix
`ρ`; it involves no trace. It is stated in operators because Fano coefficients have no finite form
for infinite-dimensional `H`. `g` and `G ρ` need not be trace class separately, so the second part
is not an expansion of `tr_B` term by term. -/
theorem eq_25 (E : AffineAssignment a H) (U : unitary (Composite a H →L[ℂ] Composite a H)) :
    (∀ ρ : Matrix a a ℂ, E.correlation ρ =
      E.g + E.G ρ - tensorOp ρ (trA E.g) - tensorOp ρ (trA (E.G ρ))) ∧
    ∃ (X₀ : Matrix a a ℂ) (X₁ : Matrix a a ℂ →ₗ[ℝ] Matrix a a ℂ)
      (X₂ : Matrix a a ℂ →ₗ[ℝ] Matrix a a ℂ →ₗ[ℝ] Matrix a a ℂ),
      ∀ ρ ∈ E.V, inhomogeneousPart E U ρ = X₀ + X₁ ρ + X₂ ρ ρ := by sorry

end AccessibleMaps
