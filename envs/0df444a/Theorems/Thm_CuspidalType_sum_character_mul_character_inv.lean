-- Prove2me | Theorems.Thm_CuspidalType_sum_character_mul_character_inv
-- name    : CuspidalType.sum_character_mul_character_inv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/de34ab6d-4ced-55e1-9516-a6ecff17fef9
-- title:
--   Self-orthogonality of an irreducible character of GL₂(𝔽_q)
-- statement:
--   Let $q$ be a prime, so that $\mathbb{Z}/q$ is the field $\mathbb{F}_q$, and write $\mathrm{GL}_2(\mathbb{F}_q)$ for the group `GL2 q` of invertible $2\times 2$ matrices over $\mathbb{Z}/q$. Let $K$ be an algebraically closed field of characteristic zero and let $V$ be a non-trivial finite-dimensional $K$-vector space, and let $\rho$ be a representation of $\mathrm{GL}_2(\mathbb{F}_q)$ on $V$ over $K$. Assume that $\rho$ is irreducible in the form: for every subrepresentation $W$ of $\rho$, if the underlying submodule of $W$ is not the zero submodule then it is all of $V$. Then, with $\chi = \rho.\mathrm{character}$ the trace character of $\rho$, the sum over all $g \in \mathrm{GL}_2(\mathbb{F}_q)$ of $\chi(g)\,\chi(g^{-1})$ equals the cardinality of $\mathrm{GL}_2(\mathbb{F}_q)$, viewed as an element of $K$ through the canonical map from the natural numbers. The sum is a finite sum over the whole group.
--
--   This is the orthogonality relation of an irreducible character with itself, $\langle \chi, \chi\rangle = 1$ rewritten without the normalising factor $1/|G|$, specialised to $G = \mathrm{GL}_2(\mathbb{F}_q)$. It serves as an input to the analysis of irreducible representations of $\mathrm{GL}_2(\mathbb{F}_q)$, being cited in the construction of a cuspidal type from an irreducible representation that is cuspidal and has central character.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspidalType_sum_character_mul_character_inv.lean

import Definitions.Def_CuspidalType_IsCuspidalOfType
import Mathlib.RepresentationTheory.Character

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CuspidalType

theorem CuspidalType.sum_character_mul_character_inv
    {q : ℕ} [Fact q.Prime] {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Nontrivial V]
    (ρ : Representation K (GL2 q) V)
    (hirr : ∀ W : Subrepresentation ρ, W.toSubmodule ≠ ⊥ → W.toSubmodule = ⊤) :
    ∑ g : GL2 q, ρ.character g * ρ.character g⁻¹ = Nat.card (GL2 q) := by sorry
