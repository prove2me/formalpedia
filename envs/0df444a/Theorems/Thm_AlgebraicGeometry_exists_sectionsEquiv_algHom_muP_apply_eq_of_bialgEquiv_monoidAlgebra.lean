-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_sectionsEquiv_algHom_muP_apply_eq_of_bialgEquiv_monoidAlgebra
-- name    : AlgebraicGeometry.exists_sectionsEquiv_algHom_muP_apply_eq_of_bialgEquiv_monoidAlgebra
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/a7a15b62-01eb-5f17-8fc9-fbab68be45e3
-- title:
--   ℤ[ℤ/n] represents the fppf sheaf μₙ
-- statement:
--   Let $n$ be a nonzero natural number, let $K$ be a commutative ring carrying a Hopf algebra structure over $\mathbf Z$, and let $f$ be an isomorphism of $\mathbf Z$-bialgebras from $K$ onto the group algebra $\mathbf Z[\mathrm{Multiplicative}(\mathbf Z/n)]$ of the cyclic group of order $n$. The assertion is that there is a family $e$, indexed by the schemes $T$ of the smallest universe, of isomorphisms of additive groups from the group of sections over $T$ of [`FppfKummerSES.muPAbelianSheafLifted n`](def/AlgebraicGeometry_FppfKummerProp17.html#L608) — the kernel, in sheaves of additive commutative groups on the big fppf site, of the map `gmPowSelf n` obtained by universe-lifting the $n$-th power endomorphism of the sheaf of units $\mathbf G_m$ — to `Additive (WithConv (K →ₐ[ℤ] Γ(T, ⊤)))`, that is, the set of $\mathbf Z$-algebra homomorphisms $K \to \Gamma(T,\mathcal O_T)$ with its convolution group law written additively, subject to two conditions. First, naturality: for every morphism $g : T \to T'$, every section $s$ over $T'$ and every $k \in K$, the homomorphism attached to the restriction of $s$ along $g$ sends $k$ to the image of $e_{T'}(s)(k)$ under $\Gamma(g)$. Second, normalisation at the group-like generator: for every $T$ and every section $s$, the homomorphism $e_T(s)$ sends $f^{-1}$ of the basis element indexed by $1 \in \mathbf Z/n$ to the element of $\Gamma(T,\mathcal O_T)$ underlying the unit `gmLiftedSectionUnit` carried by the image of $s$ under the kernel inclusion into the lifted $\mathbf G_m$ sheaf, evaluated at $T$.
--
--   This is the statement that the diagonalisable group scheme $D(\mathbf Z/n) = \operatorname{Spec}\mathbf Z[\mathbf Z/n]$ represents the fppf sheaf $\mu_n$ of $n$-th roots of unity, in the form used here: points of the Hopf algebra with values in $\Gamma(T,\mathcal O_T)$ under convolution, naturally in $T$, with the value at the group-like generator pinned to the unit carried by the section. It is used in the study of the Kummer sequence on the fppf site, by [`AlgebraicGeometry.exists_hom_injective_range_iff_of_sectionsEquiv_algHom_of_bialgHom_monoidAlgebra`](thm.html#AlgebraicGeometry.exists_hom_injective_range_iff_of_sectionsEquiv_algHom_of_bialgHom_monoidAlgebra) and by [`AlgebraicGeometry.nonempty_iso_or_natCard_algHom_eq_one_and_exists_shortExact_of_sectionsEquiv_convPow_of_ne_two`](thm.html#AlgebraicGeometry.nonempty_iso_or_natCard_algHom_eq_one_and_exists_shortExact_of_sectionsEquiv_convPow_of_ne_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_sectionsEquiv_algHom_muP_apply_eq_of_bialgEquiv_monoidAlgebra.lean

import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Bialgebra.Convolution
import Mathlib.RingTheory.Bialgebra.Equiv
import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
import Mathlib.Algebra.MonoidAlgebra.Basic
import Definitions.Def_AlgebraicGeometry_FppfKummerProp17

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory

theorem AlgebraicGeometry.exists_sectionsEquiv_algHom_muP_apply_eq_of_bialgEquiv_monoidAlgebra
    (n : ℕ) [NeZero n]
    (K : Type) [CommRing K] [HopfAlgebra ℤ K]
    (f : K ≃ₐc[ℤ] MonoidAlgebra ℤ (Multiplicative (ZMod n))) :
    ∃ e : ∀ T : Scheme.{0},
      ((FppfKummerSES.muPAbelianSheafLifted.{0} n).obj.obj (Opposite.op T)) ≃+
        Additive (WithConv (K →ₐ[ℤ] Γ(T, ⊤))),
      (∀ {T T' : Scheme.{0}} (g : T ⟶ T')
        (s : (FppfKummerSES.muPAbelianSheafLifted.{0} n).obj.obj (Opposite.op T')) (k : K),
        (Additive.toMul (e T ((FppfKummerSES.muPAbelianSheafLifted.{0} n).obj.map g.op s))) k
          = (Scheme.Γ.map g.op) ((Additive.toMul (e T' s)) k)) ∧
      ∀ (T : Scheme.{0}) (s : (FppfKummerSES.muPAbelianSheafLifted.{0} n).obj.obj (Opposite.op T)),
        (Additive.toMul (e T s)) (f.symm (MonoidAlgebra.single (Multiplicative.ofAdd 1) 1))
          = (FppfKummerSES.gmLiftedSectionUnit
              ((Limits.kernel.ι (FppfKummerSES.gmPowSelf.{0} n)).hom.app (Opposite.op T) s) : Γ(T, ⊤)) := by sorry
