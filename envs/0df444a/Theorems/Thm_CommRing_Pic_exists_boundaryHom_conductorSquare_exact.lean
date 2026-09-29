-- Prove2me | Theorems.Thm_CommRing_Pic_exists_boundaryHom_conductorSquare_exact
-- name    : CommRing.Pic.exists_boundaryHom_conductorSquare_exact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/bca35519-b29f-5dac-9b22-a0ddac58b209
-- title:
--   Units–Picard exact sequence of a conductor square
-- statement:
--   Let $A$ and $B$ be commutative rings with $B$ an $A$-algebra whose structure map is faithful (the $A$-action on $B$ is faithful, i.e. $\mathrm{algebraMap}\ A\ B$ is injective), and let $\mathfrak c$ be an ideal of $B$ every element of which lies in the image of $\mathrm{algebraMap}\ A\ B$; write $\mathfrak c_A$ for the contraction $\mathfrak c.\mathrm{comap}(\mathrm{algebraMap}\ A\ B)$. The assertion is that there is a monoid homomorphism $\delta \colon (B/\mathfrak c)^\times \to \mathrm{Pic}(A)$ with the following four properties. First, for every unit $u$ of $B/\mathfrak c$ there is an $A$-submodule $I$ of $B$ whose members are exactly those $x \in B$ for which $u \cdot \bar x$ lies in the image of $A$ in $B/\mathfrak c$, together with an $A$-linear isomorphism between the module underlying $\delta u$ and $I$. Second, $\delta u = 1$ if and only if $u$ factors as the product of the image under $\mathrm{Ideal.quotientMap}$ of a unit of $A/\mathfrak c_A$ with the class modulo $\mathfrak c$ of a unit of $B$. Third, a class $P \in \mathrm{Pic}(A)$ is of the form $\delta u$ if and only if both base changes $\mathrm{mapAlgebra}$ of $P$ to $B$ and to $A/\mathfrak c_A$ are trivial. Fourth, if a unit $t$ of $B$ has class modulo $\mathfrak c$ equal to the image of a unit of $A/\mathfrak c_A$, then $t$ is the image of a unit of $A$.
--
--   This is the rank-one part of Milnor patching for the cartesian (conductor) square formed by $A \to B$, $A \to A/\mathfrak c_A$, $B \to B/\mathfrak c$ and $A/\mathfrak c_A \to B/\mathfrak c$: the four clauses are exactness of $1 \to A^\times \to B^\times \times (A/\mathfrak c_A)^\times \to (B/\mathfrak c)^\times \xrightarrow{\delta} \mathrm{Pic}(A) \to \mathrm{Pic}(B) \times \mathrm{Pic}(A/\mathfrak c_A)$, with the boundary map described explicitly by the fractional-ideal-type modules $I(u)$. It is used for the computation of the Picard group of affine lines glued at a point, in [`CommRing.Pic.exists_surjective_hom_pic_twoAffineLinesGluedAt_eq_one_iff_const`](thm.html#CommRing.Pic.exists_surjective_hom_pic_twoAffineLinesGluedAt_eq_one_iff_const).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CommRing_Pic_exists_boundaryHom_conductorSquare_exact.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

theorem CommRing.Pic.exists_boundaryHom_conductorSquare_exact
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B] [FaithfulSMul A B]
    (𝔠 : Ideal B) (h𝔠 : ∀ b ∈ 𝔠, b ∈ Set.range (algebraMap A B)) :
    ∃ δ : (B ⧸ 𝔠)ˣ →* CommRing.Pic A,
      (∀ u : (B ⧸ 𝔠)ˣ, ∃ I : Submodule A B,
        (∀ x : B, x ∈ I ↔ ∃ a : A,
          (u : B ⧸ 𝔠) * Ideal.Quotient.mk 𝔠 x = Ideal.Quotient.mk 𝔠 (algebraMap A B a)) ∧
        Nonempty ((δ u : CommRing.Pic A) ≃ₗ[A] ↥I)) ∧
      (∀ u : (B ⧸ 𝔠)ˣ, δ u = 1 ↔
        ∃ (t : Bˣ) (a : (A ⧸ 𝔠.comap (algebraMap A B))ˣ),
          (u : B ⧸ 𝔠) =
            Ideal.quotientMap 𝔠 (algebraMap A B) le_rfl (a : A ⧸ 𝔠.comap (algebraMap A B)) *
              Ideal.Quotient.mk 𝔠 (t : B)) ∧
      (∀ P : CommRing.Pic A, (∃ u, δ u = P) ↔
        CommRing.Pic.mapAlgebra A B P = 1 ∧
          CommRing.Pic.mapAlgebra A (A ⧸ 𝔠.comap (algebraMap A B)) P = 1) ∧
      (∀ (t : Bˣ) (a : (A ⧸ 𝔠.comap (algebraMap A B))ˣ),
        Ideal.Quotient.mk 𝔠 (t : B) =
            Ideal.quotientMap 𝔠 (algebraMap A B) le_rfl (a : A ⧸ 𝔠.comap (algebraMap A B)) →
          ∃ s : Aˣ, algebraMap A B s = t) := by sorry
