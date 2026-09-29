-- Prove2me | Theorems.Thm_AlgebraicGeometry_TowerQuotientDatum_exists_preimage_eq_of_isPullback_of_forall_preimage_eq
-- name    : AlgebraicGeometry.TowerQuotientDatum.exists_preimage_eq_of_isPullback_of_forall_preimage_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/2974a353-6406-5a92-9d5e-c0bc3ad8dc88
-- title:
--   Base-changed tower quotient: surjectivity, closedness, orbits, open descent
-- statement:
--   Fix a commutative ring $\mathcal{O}$ with an element $\pi$, a tower of schemes $X_n$ equipped with structure morphisms $xb_n : X_n \to \operatorname{Spec}(\mathcal{O}/(\pi^{n+1}))$ and transition maps $xt_n : X_n \to X_{n+1}$, a finite group $G$ acting on each $X_n$ through homomorphisms $a_n : G \to \operatorname{Aut}(X_n)$, and a datum $D$ of type `TowerQuotientDatum` for these data: that is, a second tower $D.Y_n$ over $\mathcal{O}/(\pi^{n+1})$ with proper flat structure morphisms and transition maps forming pullback squares over the quotient maps of $\mathcal{O}$, together with morphisms $D.p_n : X_n \to D.Y_n$ which are compatible with the structure and transition maps (the squares formed by $xt_n$, $D.p_n$, $D.p_{n+1}$, $yt_n$ being pullbacks), $G$-invariant, finite, surjective, remaining epimorphisms after restriction to any open of $D.Y_n$, together with a local universal property `univ_loc` and a further axiom `fib` describing the $K$-valued points of the fibres of $D.p_n$ for a field $K$. Suppose given further towers $X'_n$, $Y'_n$, actions $a'_n : G \to \operatorname{Aut}(X'_n)$, and morphisms $p'_n : X'_n \to Y'_n$, $q_n : X'_n \to X_n$, $r_n : Y'_n \to D.Y_n$ such that for every $n$ the square with $q_n$, $p'_n$ on one side and $D.p_n$, $r_n$ on the other is a pullback, $q_n$ is $G$-equivariant ($a'_n(g)$ followed by $q_n$ equals $q_n$ followed by $a_n(g)$), and $p'_n$ is $G$-invariant ($a'_n(g)$ followed by $p'_n$ equals $p'_n$). Then for each fixed $n$: the map of underlying topological spaces induced by $p'_n$ is surjective and closed; any two points $x, x'$ of $X'_n$ with the same image under $p'_n$ satisfy $a'_n(g)(x) = x'$ for some $g \in G$; and every open $O \subseteq X'_n$ with $a'_n(g)^{-1}(O) = O$ for all $g \in G$ is the preimage $p'^{-1}_n(U')$ of some open $U' \subseteq Y'_n$.
--
--   This transports the topological content of a tower quotient — finite surjective $G$-invariant morphism whose fibres are $G$-orbits — along an arbitrary base change $r_n : Y'_n \to D.Y_n$, in the form needed to recognise $G$-stable opens of $X'_n$ as preimages of opens of $Y'_n$. It is used in the proof of [`AlgebraicGeometry.TowerQuotientDatum.univ_loc_of_isPullback_of_flat`](thm.html#AlgebraicGeometry.TowerQuotientDatum.univ_loc_of_isPullback_of_flat), where the local universal property of the quotient is propagated to base changes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_TowerQuotientDatum_exists_preimage_eq_of_isPullback_of_forall_preimage_eq.lean

import Definitions.Def_AlgebraicGeometry_TowerQuotientDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.TowerQuotientDatum.exists_preimage_eq_of_isPullback_of_forall_preimage_eq
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪)
    (X : ℕ → Scheme.{0}) (xb : ∀ n : ℕ, X n ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))
    (xt : ∀ n : ℕ, X n ⟶ X (n + 1))
    (G : Type) [Group G] [Finite G] (a : ∀ n : ℕ, G →* Aut (X n))
    (D : TowerQuotientDatum 𝒪 π X xb xt G a)
    (X' Y' : ℕ → Scheme.{0}) (a' : ∀ n : ℕ, G →* Aut (X' n))
    (p' : ∀ n : ℕ, X' n ⟶ Y' n) (q : ∀ n : ℕ, X' n ⟶ X n) (r : ∀ n : ℕ, Y' n ⟶ D.Y n)
    (hsq : ∀ n : ℕ, IsPullback (q n) (p' n) (D.p n) (r n))
    (hq_a : ∀ (n : ℕ) (g : G), (a' n g).hom ≫ q n = q n ≫ (a n g).hom)
    (hp'_inv : ∀ (n : ℕ) (g : G), (a' n g).hom ≫ p' n = p' n)
    (n : ℕ) :
    Function.Surjective (p' n).base ∧ IsClosedMap (p' n).base ∧
    (∀ x x' : X' n, (p' n).base x = (p' n).base x' → ∃ g : G, (a' n g).hom.base x = x') ∧
    (∀ O : (X' n).Opens, (∀ g : G, (a' n g).hom ⁻¹ᵁ O = O) → ∃ U' : (Y' n).Opens, (p' n) ⁻¹ᵁ U' = O) := by sorry
