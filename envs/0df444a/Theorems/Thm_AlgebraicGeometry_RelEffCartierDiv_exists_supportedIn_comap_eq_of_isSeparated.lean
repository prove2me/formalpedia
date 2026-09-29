-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_supportedIn_comap_eq_of_isSeparated
-- name    : AlgebraicGeometry.RelEffCartierDiv.exists_supportedIn_comap_eq_of_isSeparated
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/7a79d4f6-cd37-5730-8fa1-b4cb48a5cb59
-- title:
--   Extending relative effective divisors along an open immersion
-- statement:
--   Fix schemes $\mathcal X$, $S$ and a separated morphism $c \colon \mathcal X \to S$, an open subscheme $U \subseteq \mathcal X$ with inclusion `U.ι`, a natural number $r$, and a further scheme $T$ with a morphism $g \colon T \to S$. Let $j$ denote the canonical morphism $\mathrm{pullback}(U.\iota \circ c\text{-composite}, g) \to \mathrm{pullback}(c,g)$ obtained from `U.ι`, $\mathrm{id}_T$ and $\mathrm{id}_S$ by functoriality of the fibre product, i.e. the base change of the open immersion $U \hookrightarrow \mathcal X$ along $g$. Suppose given $D$, a relative effective Cartier divisor of degree $r$ for `U.ι ≫ c` and $g$: that is, an ideal sheaf datum $D.I$ on $U \times_S T$ whose closed subscheme inclusion, composed with the second projection to $T$, is finite, flat and locally of finite presentation, and has fibre rank exactly $r$ at every point $t \in T$. The assertion is that there exists a relative effective Cartier divisor $D'$ of degree $r$ for $c$ and $g$ — so an ideal sheaf datum on $\mathcal X \times_S T$ with the same four properties over $T$ — such that the support of $D'.I$ is contained in the preimage of $U$ under the first projection $\mathcal X \times_S T \to \mathcal X$, the comap of $D'.I$ along $j$ equals $D.I$, and $D'.I$ is the image ideal sheaf datum of $D.I$ under $j$.
--
--   This is the standard statement that a relative effective divisor on an open part $U \times_S T$ of a separated family extends uniquely to one on $\mathcal X \times_S T$ whose support lies over $U$, the extension being given by pushing forward the ideal along the open immersion. It is used in [`AlgebraicGeometry.RelEffCartierDiv.exists_supportedIn_I_eq_mul_of_supportedIn`](thm.html#AlgebraicGeometry.RelEffCartierDiv.exists_supportedIn_I_eq_mul_of_supportedIn), in the development of relative divisors needed for the modular-curve input to the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelEffCartierDiv_exists_supportedIn_comap_eq_of_isSeparated.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.RelEffCartierDiv.exists_supportedIn_comap_eq_of_isSeparated
    {𝒳 S : Scheme.{u}} {c : 𝒳 ⟶ S} [IsSeparated c] (U : 𝒳.Opens) {r : ℕ} {T : Scheme.{u}} {g : T ⟶ S}
    (D : RelEffCartierDiv (U.ι ≫ c) r g) :
    ∃ D' : RelEffCartierDiv c r g, D'.SupportedIn U ∧
      D'.I.comap (pullback.map (U.ι ≫ c) g c g U.ι (𝟙 T) (𝟙 S) (by simp) (by simp)) = D.I ∧
      D'.I = D.I.map (pullback.map (U.ι ≫ c) g c g U.ι (𝟙 T) (𝟙 S) (by simp) (by simp)) := by sorry
