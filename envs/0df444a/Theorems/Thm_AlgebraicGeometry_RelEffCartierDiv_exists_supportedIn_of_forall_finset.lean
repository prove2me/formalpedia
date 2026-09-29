-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_supportedIn_of_forall_finset
-- name    : AlgebraicGeometry.RelEffCartierDiv.exists_supportedIn_of_forall_finset
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/98e1c33a-6bbd-5e54-9e58-d4553d8ac1f9
-- title:
--   Affine charts supporting a relative divisor exist locally on T
-- statement:
--   Let $f \colon \mathcal{C} \to S$ be a morphism of schemes satisfying the following covering hypothesis: for every affine open $V \subseteq S$ and every finite set $F$ of points of $\mathcal{C}$ with $f(x) \in V$ for all $x \in F$, there is an open $U \subseteq \mathcal{C}$ that is affine, satisfies $U \le f^{-1}V$, and contains every point of $F$. Fix $r \in \mathbb{N}$, a scheme $T$ with a morphism $g \colon T \to S$, and a relative effective Cartier divisor $D$ of degree $r$ on $f$ over $g$, that is, a quasi-coherent ideal sheaf datum $D.I$ on $\mathcal{C} \times_S T$ whose associated closed subscheme, composed with the second projection to $T$, is finite, flat and locally of finite presentation and has fibre rank $r$ at every point of $T$. Then for every $t \in T$ there exist an open $W \subseteq T$ with $t \in W$, an affine open $V \subseteq S$ and an affine open $U \subseteq \mathcal{C}$ with $U \le f^{-1}V$, such that the pullback of $D$ along the inclusion $W \hookrightarrow T$ (as a divisor over $W \to T \to S$) is supported in $U$: the support of the ideal sheaf obtained by comap along $\mathcal{C} \times_S W \to \mathcal{C} \times_S T$ is contained in the preimage of $U$ under the first projection.
--
--   This is the statement that the affine charts $\mathrm{Div}^r_{U/V}$, for $U \subseteq f^{-1}V$ affine over an affine $V \subseteq S$, jointly cover the functor of relative effective Cartier divisors of degree $r$ Zariski-locally on the test scheme. It supplies the joint-surjectivity input for [`AlgebraicGeometry.RelEffCartierDiv.exists_isUniversal`](thm.html#AlgebraicGeometry.RelEffCartierDiv.exists_isUniversal), the representability of that functor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelEffCartierDiv_exists_supportedIn_of_forall_finset.lean

import Mathlib.AlgebraicGeometry.Sites.Representability
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.RelEffCartierDiv.exists_supportedIn_of_forall_finset
    {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S)
    (hcov : ∀ (V : S.affineOpens) (F : Finset 𝒞), (∀ x ∈ F, f x ∈ (V : S.Opens)) →
      ∃ U : 𝒞.Opens, IsAffineOpen U ∧ U ≤ f ⁻¹ᵁ (V : S.Opens) ∧ ∀ x ∈ F, x ∈ U)
    (r : ℕ) {T : Scheme.{u}} {g : T ⟶ S} (D : RelEffCartierDiv f r g) (t : T) :
    ∃ (W : T.Opens) (_ : t ∈ W) (V : S.affineOpens) (U : 𝒞.affineOpens)
      (_ : (U : 𝒞.Opens) ≤ f ⁻¹ᵁ (V : S.Opens)),
      (D.pullbackAlong W.ι rfl).SupportedIn U := by sorry
