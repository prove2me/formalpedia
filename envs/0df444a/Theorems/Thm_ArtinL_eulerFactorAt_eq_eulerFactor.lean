-- Prove2me | Theorems.Thm_ArtinL_eulerFactorAt_eq_eulerFactor
-- name    : ArtinL.eulerFactorAt_eq_eulerFactor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/d580b6af-1690-5031-adbd-385ccc0777f5
-- title:
--   Independence of the Artin Euler factor at p from place and Frobenius
-- statement:
--   Let $n$ be a natural number and let $\rho$ be a monoid homomorphism from $\Gamma_{\mathbb Q} = \mathrm{Aut}_{\mathbb Q}(\overline{\mathbb Q})$, the group of $\mathbb Q$-algebra automorphisms of `AlgebraicClosure ℚ`, to $\mathrm{GL}_n(\mathbb C)$, acting on $V = \mathbb C^n$ through the linear representation [`Deformation.matrixRepresentation ρ`](def/Deformations_MatrixRepresentation.html#L15). Let $p$ be a prime, let $A$ be a valuation subring of $\overline{\mathbb Q}$ lying over $p$ in the sense that the image of $p$ in $\overline{\mathbb Q}$ is a nonunit of $A$, and let $\sigma \in \Gamma_{\mathbb Q}$ be a Frobenius element at $A$ for $p$, i.e. $\sigma$ lies in the decomposition subgroup of $A$ over $\mathbb Q$ and the induced action on the residue field of $A$ is $x \mapsto x^{p}$. Write $V^{I_A}$ for the subspace of $V$ of vectors fixed by $\rho$ on the inertia subgroup of $A$ over $\mathbb Q$, viewed inside $\Gamma_{\mathbb Q}$. The conclusion is twofold: first, $\rho(\sigma)$ maps $V^{I_A}$ into itself; second, the Euler factor of $\rho$ computed at the pair $(A,\sigma)$ — namely the reversed characteristic polynomial $\det(1 - X\,\rho(\sigma)\mid V^{I_A})$, taken through the matrix of the restriction in a finite basis of $V^{I_A}$ — equals [`ArtinL.eulerFactor ρ p`](def/ArtinL_EulerFactor.html#L86), the same quantity formed from an arbitrary choice of a valuation subring over $p$ together with a Frobenius element there (and $1$ if no such pair exists).
--
--   This is the well-definedness of the local factor $\det(1 - p^{-s}\rho(\mathrm{Frob}_p)\mid V^{I_p})^{-1}$ of an Artin $L$-function at $p$: the polynomial depends only on $p$, not on the chosen place above $p$ nor on the chosen Frobenius element there. It is used to identify Euler factors of weight-one forms with those of the associated complex Galois representations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ArtinL_eulerFactorAt_eq_eulerFactor.lean

import Mathlib
import Definitions.Def_ArtinL_EulerFactor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem ArtinL.eulerFactorAt_eq_eulerFactor {n : ℕ} (ρ : Γℚ →* GL (Fin n) ℂ)
    {p : ℕ} (hp : p.Prime) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (σ : Γℚ) (hσ : A.IsFrobeniusAt σ p) :
    (∀ v ∈ ArtinL.inertiaInvariants ρ A,
        Deformation.matrixRepresentation ρ σ v ∈ ArtinL.inertiaInvariants ρ A) ∧
      ArtinL.eulerFactorAt ρ A σ = ArtinL.eulerFactor ρ p := by sorry
