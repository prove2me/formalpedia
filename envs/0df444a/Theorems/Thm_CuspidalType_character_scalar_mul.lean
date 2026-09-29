-- Prove2me | Theorems.Thm_CuspidalType_character_scalar_mul
-- name    : CuspidalType.character_scalar_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/627d517f-3385-5030-9f9e-271cbc56a01a
-- title:
--   Characters with trivial scalar action are invariant under scalars
-- statement:
--   Let $q$ be a prime, $K$ a field, and $V$ a $K$-vector space (no finiteness assumption is imposed on $V$). Let $\rho$ be a $K$-linear representation of the group $\mathrm{GL}_2(\mathbb{Z}/q) =$ `GL2 q`, the group of invertible $2\times 2$ matrices over $\mathbb{Z}/q$, on $V$. Write $\mathrm{scalarElem}\,q\,c$ for the image of a unit $c \in (\mathbb{Z}/q)^\times$ under the monoid homomorphism induced by the scalar-matrix ring homomorphism, i.e. the invertible matrix $c\cdot I_2$. Assume that $\rho$ kills all scalars in the strong sense that for every $c \in (\mathbb{Z}/q)^\times$ the endomorphism $\rho(c\cdot I_2)$ is literally the identity map of $V$. Then for every $c \in (\mathbb{Z}/q)^\times$ and every $g \in \mathrm{GL}_2(\mathbb{Z}/q)$ the character of $\rho$, that is the trace of the endomorphism $\rho(\,\cdot\,)$ of $V$, satisfies $\chi_\rho(c\cdot I_2 \cdot g) = \chi_\rho(g)$. Since $V$ is not assumed finite-dimensional, the traces are understood in Mathlib's sense, which vanishes when $V$ admits no suitable finite basis; the identity holds in either case.
--
--   This is the elementary invariance of the character of a representation with trivial action of the scalar (central) subgroup under left translation by scalar matrices; it reduces character computations for $\mathrm{GL}_2(\mathbb{F}_q)$ to the quotient by the scalars. It is used in the analysis of cuspidal types, in [`CuspidalType.IsCuspidalOfType.exists_linearEquiv_comm_of_isCuspidalOfType`](thm.html#CuspidalType.IsCuspidalOfType.exists_linearEquiv_comm_of_isCuspidalOfType).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspidalType_character_scalar_mul.lean

import Definitions.Def_CuspidalType_IsCuspidalOfType
import Mathlib.RepresentationTheory.Character

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CuspidalType

theorem CuspidalType.character_scalar_mul
    {q : ℕ} [Fact q.Prime] {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Representation K (GL2 q) V)
    (hcent : ∀ c : (ZMod q)ˣ, ρ (scalarElem q c) = LinearMap.id) (c : (ZMod q)ˣ) (g : GL2 q) :
    ρ.character (scalarElem q c * g) = ρ.character g := by sorry
