-- Prove2me | Theorems.Thm_Algebra_exists_finset_forall_exists_subalgebra_isPushout_of_span_eq_top
-- name    : Algebra.exists_finset_forall_exists_subalgebra_isPushout_of_span_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/1ca8973e-6391-5a3e-bba3-9624462d1b4d
-- title:
--   Descent of a finite projective algebra to a finitely generated subring
-- statement:
--   Let $S$ and $T$ be commutative rings with $T$ an $S$-algebra which is projective as an $S$-module, let $\iota$ be a finite index type, and let $g : \iota \to T$ be a family whose $S$-span is all of $T$, i.e. $\operatorname{span}_S(\operatorname{range} g) = \top$. Then there is a finite subset $c \subseteq S$ such that for every subring $S_0$ of $S$ (a $\mathbb{Z}$-subalgebra of $S$) with $c \subseteq S_0$ there exists an $S_0$-subalgebra $T_0$ of $T$ with the following properties: the underlying $S_0$-submodule of $T_0$ is exactly the $S_0$-span of the range of $g$, so $T_0 = \sum_i S_0\,g_i$ is closed under multiplication; $T_0$ is a finitely generated and projective $S_0$-module; if moreover the family $g$ is linearly independent over $S$, then $T_0$ is a free $S_0$-module; and the square formed by $S_0 \to S$ and $S_0 \to T_0$ is a pushout of commutative rings in the sense of `Algebra.IsPushout S₀ S T₀ T`, that is, the canonical map $S \otimes_{S_0} T_0 \to T$ is an isomorphism. The finite set $c$ of structure constants is chosen once and for all, independently of $S_0$.
--
--   This is the affine, finite locally free instance of Grothendieck's principle that data of finite presentation over a commutative ring are already defined over a finitely generated subring: the multiplication table and the coefficients expressing $1$ and a projectivity splitting in terms of $g$ involve only finitely many elements of $S$, and any subring containing them supports a model $T_0$ with $T = S \otimes_{S_0} T_0$. Taking $S_0 = \mathbb{Z}[c]$ gives a noetherian base, which is how statements about finite projective algebras over a general base are reduced to the noetherian case; it is used in the construction of a prime of a finite faithfully flat algebra avoiding a given element, over a base obtained by localisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_exists_finset_forall_exists_subalgebra_isPushout_of_span_eq_top.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem Algebra.exists_finset_forall_exists_subalgebra_isPushout_of_span_eq_top
    {S T : Type} [CommRing S] [CommRing T] [Algebra S T] [Module.Projective S T]
    {ι : Type} [Finite ι] (g : ι → T) (hg : Submodule.span S (Set.range g) = ⊤) :
    ∃ c : Finset S, ∀ S₀ : Subalgebra ℤ S, ↑c ⊆ (S₀ : Set S) →
      ∃ T₀ : Subalgebra S₀ T, Subalgebra.toSubmodule T₀ = Submodule.span S₀ (Set.range g) ∧
        Module.Finite S₀ T₀ ∧ Module.Projective S₀ T₀ ∧
        (LinearIndependent S g → Module.Free S₀ T₀) ∧ Algebra.IsPushout S₀ S T₀ T := by sorry
