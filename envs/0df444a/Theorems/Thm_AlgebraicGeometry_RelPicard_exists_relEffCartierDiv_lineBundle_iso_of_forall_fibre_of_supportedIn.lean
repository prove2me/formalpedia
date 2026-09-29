-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_relEffCartierDiv_lineBundle_iso_of_forall_fibre_of_supportedIn
-- name    : AlgebraicGeometry.RelPicard.exists_relEffCartierDiv_lineBundle_iso_of_forall_fibre_of_supportedIn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/adbff894-03ab-598c-b718-84452ae657ef
-- title:
--   Section theorem: relative divisor attached to a fibrewise h⁰=1 bundle
-- statement:
--   Let $R$ be a Noetherian commutative ring, let $c\colon C\to\operatorname{Spec}R$ be proper and flat, let $U\subseteq C$ be an open subscheme such that the composite $U\hookrightarrow C\to\operatorname{Spec}R$ is smooth of relative dimension $1$, and let $g\in\mathbb N$. Two hypotheses are assumed as named inputs, for every scheme $T$ with a morphism $t$ to $\operatorname{Spec}R$ locally of finite type and every invertible module $F$ on $C\times_{\operatorname{Spec}R}T$ (invertible meaning: every point has an open neighbourhood on which the restriction is isomorphic to the unit module): `hpush` says that if, for every field $k$, every $s\colon\operatorname{Spec}k\to T$ and every two-chart affine open cover of the fibre $\operatorname{pullback}(\mathrm{pr}_2,s)$, the two-term Čech complex of the sections of the fibre module $F_s$ has vanishing (subsingleton) $H^1$ and $H^0$ of $k$-dimension $n$, then $\mathrm{pr}_{2*}F$ is locally free of rank $n$ (each point has a neighbourhood on which it is isomorphic to the free module on $n$ generators); `hcounit` says that under the same Čech conditions with $n=1$, for every field $k$ and every $x\colon\operatorname{Spec}k\to T$ the pullback along `mapOnProdOver c x rfl` of the counit $\mathrm{pr}_2^*\mathrm{pr}_{2*}F\to F$ of the pullback–pushforward adjunction is nonzero. Now let $t\colon T\to\operatorname{Spec}R$ be locally of finite type and let $M$ be an invertible module on $C\times_{\operatorname{Spec}R}T$ satisfying the above Čech conditions with $n=1$ at all field-valued points of $T$, and assume `hZfib`: for every algebraically closed field $k$, every $x\colon\operatorname{Spec}k\to T$ and every nonzero morphism $\sigma$ from the unit module to the pullback of $M$ to $C\times_{\operatorname{Spec}R}\operatorname{Spec}k$, there is a relative effective Cartier divisor $D_x$ for $c$ of degree $g$ over $x\circ t$ — that is, an ideal sheaf datum whose closed subscheme is finite, flat and locally of finite presentation over the base with fibre rank $g$ at every point — whose ideal is the zero-scheme ideal of $\sigma$ and whose support lies in the preimage of $U$ under the first projection. The conclusion: there exist a relative effective Cartier divisor $D$ for $c$ of degree $g$ over $t$ and an invertible module $N$ on $T$ such that the line bundle $\mathcal O(D)$ (the inverse module of $D.I$) is isomorphic to $M\otimes\mathrm{pr}_2^*N$, and such that for every $d'\in\mathbb N$, every relative effective Cartier divisor $D'$ of degree $d'$ over $t$ supported in $U$ and every invertible $N'$ on $T$ with $\mathcal O(D')\cong M\otimes\mathrm{pr}_2^*N'$, one has $D'.I=D.I$. Note that the exhibited $D$ is itself not asserted in the conclusion to be supported in $U$.
--
--   This is the section theorem in the form used to compare effective relative divisors with invertible modules on a proper flat family of curves: a fibrewise condition $H^1=0$, $h^0=1$ produces a single relative effective divisor of degree $g$ realising $M$ up to a twist from the base, uniquely determined among divisors supported in the smooth locus $U$. The cohomology and base-change inputs are taken as hypotheses (`hpush`, `hcounit`), so that the statement can be applied to families built from explicit two-chart covers; it is used in the proofs that suitable relative sub-Picard functors of two-glued smooth curve degenerations, and of two-line degenerations, are represented by the zero-cut construction after base change away from a prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_relEffCartierDiv_lineBundle_iso_of_forall_fibre_of_supportedIn.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra

theorem AlgebraicGeometry.RelPicard.exists_relEffCartierDiv_lineBundle_iso_of_forall_fibre_of_supportedIn
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [Flat c]
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)] (g : ℕ)

    (hpush : ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
      (F : (pullback c t).Modules), Scheme.Modules.IsInvertible F → ∀ (n : ℕ),
      (∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T) (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s F)).H1 ∧
          Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s F)).H0 = n) →
      Scheme.Modules.IsLocallyFreeOfRank n ((Scheme.Modules.pushforward (pullback.snd c t)).obj F))

    (hcounit : ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
      (F : (pullback c t).Modules), Scheme.Modules.IsInvertible F →
      (∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T) (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s F)).H1 ∧
          Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s F)).H0 = 1) →
      ∀ {k : Type u} [Field k] (x : Spec (CommRingCat.of k) ⟶ T),
        (Scheme.Modules.pullback (mapOnProdOver c x rfl)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction (pullback.snd c t)).counit.app F) ≠ 0)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
    (M : (pullback c t).Modules) (hM : Scheme.Modules.IsInvertible M)
    (hfib : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
      (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H1 ∧
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H0 = 1)

    (hZfib : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ T)
      (σ : 𝟙_ (pullback c (x ≫ t)).Modules ⟶ (Scheme.Modules.pullback (mapOnProdOver c x rfl)).obj M), σ ≠ 0 →
      ∃ Dx : RelEffCartierDiv c g (x ≫ t), Dx.I = Scheme.Modules.zeroSchemeIdeal σ ∧ Dx.SupportedIn U) :
    ∃ (D : RelEffCartierDiv c g t) (N : T.Modules), Scheme.Modules.IsInvertible N ∧
      Nonempty (D.lineBundle ≅ M ⊗ (Scheme.Modules.pullback (pullback.snd c t)).obj N) ∧
      ∀ (d' : ℕ) (D' : RelEffCartierDiv c d' t) (N' : T.Modules), Scheme.Modules.IsInvertible N' → D'.SupportedIn U →
        Nonempty (D'.lineBundle ≅ M ⊗ (Scheme.Modules.pullback (pullback.snd c t)).obj N') → D'.I = D.I := by sorry
