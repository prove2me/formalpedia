-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_relEffCartierDiv_supportedIn_twistModule_iso_of_subsingleton_H1_of_zeroScheme
-- name    : AlgebraicGeometry.RelPicard.exists_relEffCartierDiv_supportedIn_twistModule_iso_of_subsingleton_H1_of_zeroScheme
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/acd3c3cc-fd97-571e-8070-54f837b022c6
-- title:
--   Existence of D=D₀+D_γ trivialising the twist of L
-- statement:
--   Fix a commutative ring $R$, a separated morphism $c\colon C\to\operatorname{Spec}R$, a section $\varepsilon$ of $c$, and an open $U\subseteq C$ with $U\hookrightarrow C\to\operatorname{Spec}R$ smooth of relative dimension $1$ and $\operatorname{range}\varepsilon\subseteq U$; fix $g,e,r$ with $g+e=r$ and a relative effective Cartier divisor $D_\gamma$ of degree $e$ over $\operatorname{Spec}R$ (a finite, flat, locally finitely presented ideal subscheme of $C$ of fibre rank $e$) whose support lies in the preimage of $U$. Write $M_\gamma(L)=L.L\otimes(\mathrm{sectionTwist}\,c\,\varepsilon\,t\,r\otimes(D_\gamma)_T^{\,\mathrm{ideal}})$, where $\mathrm{sectionTwist}$ is the inverse module of the $r$-th power of the kernel ideal of the rigidifying section and $(D_\gamma)_T^{\,\mathrm{ideal}}$ the ideal module of the base change of $D_\gamma$. Four hypotheses are assumed: (i) a section principle: for every $u\colon V\to\operatorname{Spec}R$ locally of finite type and every invertible $M$ on $C\times_RV$ such that on every field-valued fibre and every two-affine open cover the Čech $H^1$ of the sections of the fibre module vanishes and $H^0$ has $k$-rank $1$, and such that over every algebraically closed point every nonzero map from the unit module to the pulled-back $M$ has zero-scheme ideal equal to the ideal of a degree-$g$ relative effective Cartier divisor supported in $U$, there exist a degree-$g$ divisor $D_0$ over $u$ and an invertible $N$ on $V$ with $\mathcal O(D_0)=D_0.\mathrm{lineBundle}\cong M\otimes\mathrm{pr}_2^*N$, and any $D'$ supported in $U$ with $D'.\mathrm{lineBundle}\cong M\otimes\mathrm{pr}_2^*N'$ for invertible $N'$ satisfies $D'.I=D_0.I$; (ii) for every $t\colon T\to\operatorname{Spec}R$ locally of finite type and every rigidified line bundle $L$ on $C\times_RT$ that is fibrewise algebraically equivalent to zero, nonzero sections of $M_\gamma(L)$ over algebraically closed points cut out degree-$g$ divisors supported in $U$; (iii) for such $L$, vanishing of the Čech $H^1$ of $M_\gamma(L)$ on a field-valued fibre forces $H^0$ to have rank $1$; (iv) any degree-$g$ divisor $D_0$ over such a $t$ with $D_0.\mathrm{lineBundle}\cong M_\gamma(L)\otimes\mathrm{pr}_2^*N$, $N$ invertible, is supported in $U$. Let then $t\colon T\to\operatorname{Spec}R$ be locally of finite type, $L$ a rigidified line bundle on $C\times_RT$ fibrewise algebraically equivalent to zero, and $W\subseteq T$ open such that for every field $k$ and every $s\colon\operatorname{Spec}k\to T$ with image in $W$ the Čech $H^1$ of $M_\gamma(L)$ on the fibre at $s$ vanishes for every two-affine open cover. The conclusion: there are relative effective Cartier divisors $D$ of degree $r$ and $D_0$ of degree $g$ over $W\hookrightarrow T\to\operatorname{Spec}R$ such that $D.I=D_0.I\cdot(D_\gamma)_W.I$, the twist module $D.\mathrm{twistModule}\,c\,\varepsilon$ (the rigidification along the section of $D.\mathrm{lineBundle}\otimes(\mathrm{sectionIdeal}^r).\mathrm{module}$) is isomorphic to the restriction of $L$ to $W$, and $D_0$ is supported in $U$.
--
--   This is the existence half of the open-chart construction for the relative Picard functor in the semistable setting, where smoothness and geometric integrality of the whole curve are replaced by the smooth open $U$ carrying $\varepsilon$ and $D_\gamma$ together with the four named hypotheses: over the locus $W$ where fibrewise $\check H^1$ vanishes, each rigidified line bundle algebraically equivalent to zero is the $r\varepsilon$-twist of $\mathcal O(D)$ with $D=D_0+D_\gamma$ and $D_0$ supported in $U$. It feeds the construction of open charts, by open immersions, for the algebraic-equivalence-zero cut of the relative sub-Picard presheaf.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_relEffCartierDiv_supportedIn_twistModule_iso_of_subsingleton_H1_of_zeroScheme.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivTwist2
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra
open AlgebraicGeometry.RelPicard

theorem AlgebraicGeometry.RelPicard.exists_relEffCartierDiv_supportedIn_twistModule_iso_of_subsingleton_H1_of_zeroScheme
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)] (hεU : Set.range ε.1 ⊆ (U : Set C))
    (g e r : ℕ) (hr : g + e = r) (Dγ : RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of R)))) (hDγ : Dγ.SupportedIn U)

    (hsect : ∀ ⦃V : Scheme.{u}⦄ (u : V ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType u] (M : (pullback c u).Modules),
      Scheme.Modules.IsInvertible M →
      (∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ V) (𝒲 : (pullback (pullback.snd c u) s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c u s) (fibreModule c u s M)).H1 ∧
          Module.finrank k (𝒲.sectionsOf (fibreAt c u s) (fibreModule c u s M)).H0 = 1) →
      (∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ V)
        (σ : 𝟙_ (pullback c (x ≫ u)).Modules ⟶ (Scheme.Modules.pullback (mapOnProdOver c x rfl)).obj M), σ ≠ 0 →
        ∃ Dx : RelEffCartierDiv c g (x ≫ u), Dx.I = Scheme.Modules.zeroSchemeIdeal σ ∧ Dx.SupportedIn U) →
      ∃ (D₀ : RelEffCartierDiv c g u) (N : V.Modules), Scheme.Modules.IsInvertible N ∧
        Nonempty (D₀.lineBundle ≅ M ⊗ (Scheme.Modules.pullback (pullback.snd c u)).obj N) ∧
        ∀ (d' : ℕ) (D' : RelEffCartierDiv c d' u) (N' : V.Modules), Scheme.Modules.IsInvertible N' → D'.SupportedIn U →
          Nonempty (D'.lineBundle ≅ M ⊗ (Scheme.Modules.pullback (pullback.snd c u)).obj N') → D'.I = D₀.I)

    (hZfibγ : ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
      (L : RigidifiedLineBundle c ε t), FibrewiseAlgEquivZero L →
      ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ T)
        (σ : 𝟙_ (pullback c (x ≫ t)).Modules ⟶ (Scheme.Modules.pullback (mapOnProdOver c x rfl)).obj
          (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule))), σ ≠ 0 →
        ∃ Dx : RelEffCartierDiv c g (x ≫ t), Dx.I = Scheme.Modules.zeroSchemeIdeal σ ∧ Dx.SupportedIn U)

    (hH0one : ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)) (L : RigidifiedLineBundle c ε t), FibrewiseAlgEquivZero L →
      ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T) (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
          (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)))).H1 →
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
          (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)))).H0 = 1)

    (havoid : ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
      (L : RigidifiedLineBundle c ε t), FibrewiseAlgEquivZero L →
      ∀ (D₀ : RelEffCartierDiv c g t) (N : T.Modules), Scheme.Modules.IsInvertible N →
        Nonempty (D₀.lineBundle ≅
          (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)) ⊗
            (Scheme.Modules.pullback (pullback.snd c t)).obj N) →
        D₀.SupportedIn U)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
    (L : RigidifiedLineBundle c ε t) (hL : FibrewiseAlgEquivZero L) (W : T.Opens)
    (hW : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T), Set.range ⇑s ⊆ (W : Set T) →
      ∀ (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
          (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)))).H1) :
    ∃ (D : RelEffCartierDiv c r (W.ι ≫ t)) (D₀ : RelEffCartierDiv c g (W.ι ≫ t)),
      D.I = D₀.I * (Dγ.pullbackAlong (W.ι ≫ t) (Category.comp_id _)).I ∧
      Nonempty (D.twistModule c ε ≅ (L.pullbackAlong (⟨W.ι, rfl⟩ : SchemeHomOver (W.ι ≫ t) t)).L) ∧
      D₀.SupportedIn U := by sorry
