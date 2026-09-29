-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_supportedIn_of_lineBundle_iso_of_forall_zeroScheme_supportedIn
-- name    : AlgebraicGeometry.RelEffCartierDiv.supportedIn_of_lineBundle_iso_of_forall_zeroScheme_supportedIn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/63ec28fb-8a58-5f4d-b3c0-5739159dc9f5
-- title:
--   Fibrewise zero-scheme criterion for support of a relative divisor
-- statement:
--   Let $R$ be a commutative ring, let $c \colon C \to \operatorname{Spec} R$ be a morphism of schemes, let $U$ be an open subscheme of $C$, and let $t \colon T \to \operatorname{Spec} R$ be a further $R$-scheme. Let $M$ be a module on the fibre product $C \times_{\operatorname{Spec} R} T$ which is invertible in the sense of `Scheme.Modules.IsInvertible`, namely every point has an open neighbourhood $V$ on which the restriction of $M$ is isomorphic to the unit sheaf of modules of $V$. Let $g$ be a natural number and let $D_0$ be a relative effective Cartier divisor of degree $g$ for $c$ over $t$: an ideal sheaf datum $I$ on $C \times_{\operatorname{Spec} R} T$ whose closed subscheme inclusion followed by the second projection to $T$ is finite, flat and locally of finite presentation, with fibre rank $g$ at every point of $T$. Let $N$ be an invertible module on $T$, and assume that the line bundle of $D_0$, i.e. the dual of the module of $I$, is isomorphic to $M \otimes \operatorname{pr}_2^{*} N$. Assume further that for every algebraically closed field $k$, every $k$-point $x \colon \operatorname{Spec} k \to T$ and every nonzero morphism $\sigma$ from the unit object of the modules on $C \times_{\operatorname{Spec} R} \operatorname{Spec} k$ to the pullback of $M$ along the induced map `mapOnProdOver c x rfl`, there is a relative effective Cartier divisor $D_x$ of degree $g$ for $c$ over $x \circ t$ whose ideal sheaf datum is the zero-scheme ideal of $\sigma$ — the infimum of those ideal sheaf data $J$ with $\operatorname{span}(\operatorname{range}(\operatorname{coeff} \sigma\, V)) \le J(V)$ for all affine opens $V$ — and whose support is contained in the preimage of $U$ under the first projection. The conclusion is that $D_0$ is supported in $U$, i.e. the support of $I$, viewed as a subset of $C \times_{\operatorname{Spec} R} T$, is contained in the preimage of $U$ under the first projection.
--
--   This is the passage from a fibrewise hypothesis on zero schemes of sections over geometric points to a statement about the support of a relative effective divisor over the whole base, the avoidance condition needed when effective divisors are traded for sections of a line bundle. It is used in the construction of charts for the relative Picard functor, being cited in the representability results for relative sub-Picard schemes attached to two glued smooth curve degenerations and to two line degenerations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelEffCartierDiv_supportedIn_of_lineBundle_iso_of_forall_zeroScheme_supportedIn.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.RelEffCartierDiv.supportedIn_of_lineBundle_iso_of_forall_zeroScheme_supportedIn
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) (U : C.Opens)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (M : (pullback c t).Modules) (hM : Scheme.Modules.IsInvertible M)
    {g : ℕ} (D₀ : RelEffCartierDiv c g t) (N : T.Modules) (hN : Scheme.Modules.IsInvertible N)
    (hiso : Nonempty (D₀.lineBundle ≅ M ⊗ (Scheme.Modules.pullback (pullback.snd c t)).obj N))
    (hZ : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ T)
      (σ : 𝟙_ (pullback c (x ≫ t)).Modules ⟶ (Scheme.Modules.pullback (mapOnProdOver c x rfl)).obj M), σ ≠ 0 →
      ∃ Dx : RelEffCartierDiv c g (x ≫ t), Dx.I = Scheme.Modules.zeroSchemeIdeal σ ∧ Dx.SupportedIn U) :
    D₀.SupportedIn U := by sorry
