-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_mul
-- name    : AlgebraicGeometry.RelEffCartierDiv.exists_I_eq_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/df3e8c81-a043-53ba-b4cd-49a2950f474a
-- title:
--   Addition of relative effective divisors on a smooth curve
-- statement:
--   Let $f \colon \mathcal{C} \to S$ be a morphism of schemes which is separated and smooth of relative dimension $1$, let $g \colon T \to S$ be an arbitrary $S$-scheme, and let $r, s$ be natural numbers. A term of `RelEffCartierDiv f r g` consists of an ideal sheaf datum $\mathcal{I}$ on the fibre product $\mathcal{C} \times_S T$ (that is, on `pullback f g`) such that the composite of the closed immersion of the subscheme cut out by $\mathcal{I}$ with the second projection to $T$ is finite, flat and locally of finite presentation, and has fibre rank exactly $r$ at every point $t$ of $T$; similarly for $s$. Given such data $D$ of degree $r$ and $E$ of degree $s$, the theorem asserts the existence of a term $F$ of `RelEffCartierDiv f (r+s) g`, i.e. of an ideal sheaf datum on $\mathcal{C} \times_S T$ which is finite, flat, locally of finite presentation and of constant fibre rank $r+s$ over $T$, whose underlying ideal sheaf datum is the product $F.I = D.I \cdot E.I$. Only existence is asserted; no uniqueness claim is made here.
--
--   This is the additive law on relative effective Cartier divisors of a smooth relative curve: the product of the ideal sheaves of divisors of degrees $r$ and $s$ is again the ideal sheaf of a relative effective divisor, of degree $r+s$, over an arbitrary base $T$ with no Noetherian or reducedness hypothesis. It underlies the construction of sums of divisors used in the comparison of divisor classes with line bundles and in the splitting off of graph sections, being cited by [`AlgebraicGeometry.RelEffCartierDiv.exists_I_eq_prodKerGraph`](thm.html#AlgebraicGeometry.RelEffCartierDiv.exists_I_eq_prodKerGraph), [`AlgebraicGeometry.RelEffCartierDiv.exists_nonempty_tensor_lineBundle_iso_lineBundle`](thm.html#AlgebraicGeometry.RelEffCartierDiv.exists_nonempty_tensor_lineBundle_iso_lineBundle) and [`AlgebraicGeometry.RelEffCartierDiv.exists_supportedIn_I_eq_mul_of_supportedIn`](thm.html#AlgebraicGeometry.RelEffCartierDiv.exists_supportedIn_I_eq_mul_of_supportedIn).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_mul.lean

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.RelEffCartierDiv.exists_I_eq_mul
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    {r s : ℕ} {T : Scheme.{u}} {g : T ⟶ S}
    (D : RelEffCartierDiv f r g) (E : RelEffCartierDiv f s g) :
    ∃ F : RelEffCartierDiv f (r + s) g, F.I = D.I * E.I := by sorry
