-- Prove2me | Theorems.Thm_E34D_exists_ringHom_algebraicClosure_ker_eq
-- name    : E34D.exists_ringHom_algebraicClosure_ker_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/5961b5ba-d6e7-5aa9-a90a-2aebe6121f27
-- title:
--   Maximal ideals containing p as kernels of 𝔽̄ₚ-valued characters
-- statement:
--   Let $R$ be a commutative ring which is finite as a $\mathbb{Z}$-module (i.e. finitely generated as an abelian group), let $p$ be a natural number carrying the hypothesis that it is prime, and let $\mathfrak{m}$ be an ideal of $R$. Assume $\mathfrak{m}$ is maximal and that the image of $p$ under the canonical map $\mathbb{N} \to R$ lies in $\mathfrak{m}$. The conclusion asserts the existence of a ring homomorphism $\varphi : R \to \overline{\mathbb{F}}_p$, where $\overline{\mathbb{F}}_p$ is Mathlib's `AlgebraicClosure (ZMod p)`, whose kernel is exactly $\mathfrak{m}$. Thus every maximal ideal of residue characteristic $p$ in such a ring arises as the kernel of a character with values in an algebraic closure of the prime field; no uniqueness or Galois-orbit statement is made, and the homomorphism is not required to be compatible with any further structure.
--
--   This is the forward half of the standard dictionary between maximal ideals of residue characteristic $p$ in a ring finite over $\mathbb{Z}$ and characters of that ring valued in $\overline{\mathbb{F}}_p$. It is used to convert maximal-ideal data for Hecke algebras into mod $p$ eigensystems, in the passage to [`WeierstrassCurve.exists_mem_modPCusp_isModPEigen_pow_mul_apOfModel_of_ideal_heckeAlgebra`](thm.html#WeierstrassCurve.exists_mem_modPCusp_isModPEigen_pow_mul_apOfModel_of_ideal_heckeAlgebra).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_E34D_exists_ringHom_algebraicClosure_ker_eq.lean

import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.Field.ZMod

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem E34D.exists_ringHom_algebraicClosure_ker_eq {R : Type*} [CommRing R] {p : ℕ}
    [hp : Fact p.Prime] [Module.Finite ℤ R]
    {𝔪 : Ideal R} (h𝔪 : 𝔪.IsMaximal) (hp𝔪 : (p : R) ∈ 𝔪) :
    ∃ φ : R →+* AlgebraicClosure (ZMod p), RingHom.ker φ = 𝔪 := by sorry
