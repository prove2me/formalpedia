-- Prove2me | Theorems.Thm_AlgebraicGeometry_isClopen_preimage_diagonal_of_formallyUnramified_of_isSeparated
-- name    : AlgebraicGeometry.isClopen_preimage_diagonal_of_formallyUnramified_of_isSeparated
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/35df00f7-035a-506a-90b7-765467e9f18a
-- title:
--   Clopen agreement locus of two sections of an unramified separated morphism
-- statement:
--   Let $p : Z \to S$ be a morphism of schemes (in a fixed universe) which is formally unramified, locally of finite type and separated, and let $\sigma, \tau : S \to Z$ be two sections of $p$, i.e. $\sigma \circ p = \mathrm{id}_S$ and $\tau \circ p = \mathrm{id}_S$ in the sense that $\sigma$ followed by $p$ and $\tau$ followed by $p$ are both the identity of $S$. Since the two composites agree, there is an induced morphism $(\sigma,\tau) : S \to Z \times_S Z$ obtained from the universal property of the pullback, and one may form the open subset of $S$ which is the preimage under $(\sigma,\tau)$ of the open range of the diagonal $\Delta : Z \to Z \times_S Z$ — the diagonal is an open immersion under the stated hypotheses, so its set-theoretic range is an open subscheme-theoretic subset. The theorem asserts two things about the underlying set $U \subseteq S$ of that open. First, $U$ is closed as well as open, hence clopen. Second, $U$ has the expected universal property: for every scheme $T$ and every morphism $g : T \to S$, the set-theoretic image of $g$ is contained in $U$ if and only if $g$ followed by $\sigma$ equals $g$ followed by $\tau$.
--
--   This is the standard statement that two sections of a separated unramified morphism locally of finite type agree on a clopen part of the base, together with the representability of the agreement condition by that clopen subset. It is used in the construction and comparison of level structures on fake elliptic curves, where conditions such as 'a given section is annihilated by a prescribed integer' are thereby seen to be open-and-closed conditions on the base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isClopen_preimage_diagonal_of_formallyUnramified_of_isSeparated.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.isClopen_preimage_diagonal_of_formallyUnramified_of_isSeparated
    {Z S : Scheme.{u}} (p : Z ⟶ S) [FormallyUnramified p] [LocallyOfFiniteType p] [IsSeparated p]
    (σ τ : S ⟶ Z) (hσ : σ ≫ p = 𝟙 S) (hτ : τ ≫ p = 𝟙 S) :
    IsClopen ((pullback.lift σ τ (hσ.trans hτ.symm) ⁻¹ᵁ (pullback.diagonal p).opensRange : S.Opens) : Set S) ∧
    ∀ {T : Scheme.{u}} (g : T ⟶ S),
      Set.range g ⊆ (pullback.lift σ τ (hσ.trans hτ.symm) ⁻¹ᵁ (pullback.diagonal p).opensRange : Set S) ↔ g ≫ σ = g ≫ τ := by sorry
