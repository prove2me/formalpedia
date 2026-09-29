-- Prove2me | Theorems.Thm_Algebra_Etale_exists_algEquiv_residue_eq_of_isLocalRing_of_isAdicComplete
-- name    : Algebra.Etale.exists_algEquiv_residue_eq_of_isLocalRing_of_isAdicComplete
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/34ffb337-9172-5966-a4ba-89750a0ee042
-- title:
--   Lifting a residue-field isomorphism to finite étale local algebras
-- statement:
--   Let $R$ be a commutative ring that is local, Noetherian and complete for the $\mathfrak m_R$-adic topology (in Lean: `IsAdicComplete (maximalIdeal R) R`), and let $A$ and $B$ be commutative local rings, each equipped with an $R$-algebra structure which makes it a finitely generated $R$-module, which is étale over $R$, and whose structure map $R \to A$, resp. $R \to B$, is a local homomorphism (sends $\mathfrak m_R$ into the maximal ideal). All three rings lie in one universe. Write $\operatorname{ResidueField}$ for the residue field and $\mathrm{residue}$ for the quotient map onto it; the local structure maps induce $\operatorname{ResidueField} R$-algebra structures on $\operatorname{ResidueField} A$ and $\operatorname{ResidueField} B$. The hypothesis is an isomorphism $e_0 \colon \operatorname{ResidueField} A \xrightarrow{\sim} \operatorname{ResidueField} B$ of algebras over $\operatorname{ResidueField} R$. The assertion is that there exists an $R$-algebra isomorphism $e \colon A \xrightarrow{\sim} B$ which induces $e_0$ on residue fields, that is, $\mathrm{residue}_B(e(a)) = e_0(\mathrm{residue}_A(a))$ for every $a \in A$.
--
--   This is the 'isomorphisms lift' half of the equivalence between finite étale local algebras over a Henselian (here complete Noetherian) local ring and finite separable extensions of its residue field. It is used to identify a finite étale local algebra with a prescribed residue field, both in the counting form [`Algebra.Etale.nonempty_algEquiv_of_isLocalRing_of_finite_residueField_of_card_eq`](thm.html#Algebra.Etale.nonempty_algEquiv_of_isLocalRing_of_finite_residueField_of_card_eq) and in the construction of the crossing model on the modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_Etale_exists_algEquiv_residue_eq_of_isLocalRing_of_isAdicComplete.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open IsLocalRing

theorem Algebra.Etale.exists_algEquiv_residue_eq_of_isLocalRing_of_isAdicComplete
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R]
    (A B : Type u) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    [Algebra R A] [Algebra R B] [Module.Finite R A] [Module.Finite R B]
    [Algebra.Etale R A] [Algebra.Etale R B]
    [IsLocalHom (algebraMap R A)] [IsLocalHom (algebraMap R B)]
    (e₀ : ResidueField A ≃ₐ[ResidueField R] ResidueField B) :
    ∃ e : A ≃ₐ[R] B, ∀ a : A, residue B (e a) = e₀ (residue A a) := by sorry
