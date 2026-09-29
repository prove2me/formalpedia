-- Prove2me | Theorems.Thm_AlgebraicGeometry_DescentCharacter_hasValue_transport_of_pullback_map_comp_sectionScalar_eq_of_appTop_eq
-- name    : AlgebraicGeometry.DescentCharacter.hasValue_transport_of_pullback_map_comp_sectionScalar_eq_of_appTop_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/ffc2e255-38af-5f39-b679-0fc5a502eae6
-- title:
--   Transported descended isomorphism has descent-character value c
-- statement:
--   Let $X,Y,P,X',Y'$ be schemes, $R'$ a commutative ring, $q\colon X\to Y$ a morphism, and $p_1,p_2\colon P\to X$ two morphisms with $p_1\mathbin{\text{followed by}}q=p_2\mathbin{\text{followed by}}q$. Let $N,M$ be objects of `Y.Modules`, let $u\in\Gamma(P,\mathcal O_P)$, and let $\sigma$ be an endomorphism of $p_1^*q^*M$ which acts on sections by $u$: for every open $U\subseteq P$ and every $s\in\Gamma(p_1^*q^*M,U)$ one has $\sigma_U(s)=(u|_U)\cdot s$. Let $\beta\colon q^*N\cong q^*M$ be an isomorphism satisfying the cocycle-type identity $$p_1^*\beta \;;\; \sigma\;;\;\kappa_M \;=\; \kappa_N\;;\;p_2^*\beta,$$ where $\kappa_L$ denotes the canonical comparison $p_1^*q^*L\cong (p_1q)^*L=(p_2q)^*L\cong p_2^*q^*L$ built from `Scheme.Modules.pullbackComp` and the equality $p_1q=p_2q$. Further let $f'\colon X'\to\operatorname{Spec}R'$, $T'\colon X'\to X'$ and $q'\colon X'\to Y'$ with $T'q'=q'$ and $T'f'=f'$, let $g_X\colon X'\to X$, $g_Y\colon Y'\to Y$ with $g_Xq=q'g_Y$, let $s\colon X'\to P$ with $sp_1=g_X$ and $sp_2=T'g_X$, and let $c\in R'$ with $s^{\#}(u)=f'^{\#}(\iota(c))$ on global sections, $\iota$ being the inverse of `Scheme.ΓSpecIso` for $R'$. Form the transported isomorphism $\beta'\colon q'^*g_Y^*N\cong q'^*g_Y^*M$ as the composite $q'^*g_Y^*N\cong(q'g_Y)^*N\cong(g_Xq)^*N\cong g_X^*q^*N\xrightarrow{g_X^*\beta}g_X^*q^*M\cong(g_Xq)^*M\cong(q'g_Y)^*M\cong q'^*g_Y^*M$. Then `HasValue` holds for $f'$, the identity $T'q'=q'$, $\beta'$ and $c$; that is, the discrepancy endomorphism $\beta'^{-1}$ followed by the translate of $\beta'$ along $T'$ acts on every section over every open $U\subseteq X'$ as multiplication by the section `baseSection f' c U` attached to $c$ via $f'$.
--
--   This is the generic computation of the descent character: the value attached to an isomorphism descended through $q$ is the twisting function $u$ read back along a section $s$ whose two legs are the identity and the deck transformation, and it is stated here after an arbitrary base change along $(g_X,g_Y)$. It is used in the surjectivity statement [`AlgebraicGeometry.Polarisation.exists_rigidifiedLineBundle_pullback_schemeNsmul_two_trivial_hasValue_translate`](thm.html#AlgebraicGeometry.Polarisation.exists_rigidifiedLineBundle_pullback_schemeNsmul_two_trivial_hasValue_translate), where $q$ is multiplication by $2$ on an abelian scheme and $s$ is the graph of a translation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_DescentCharacter_hasValue_transport_of_pullback_map_comp_sectionScalar_eq_of_appTop_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_DescentCharacter

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry AlgebraicGeometry.DescentCharacter

universe u

theorem AlgebraicGeometry.DescentCharacter.hasValue_transport_of_pullback_map_comp_sectionScalar_eq_of_appTop_eq
    {X Y P X' Y' : Scheme.{u}} {R' : Type u} [CommRing R'] (q : X ⟶ Y)
    (p₁ p₂ : P ⟶ X) (hp : p₁ ≫ q = p₂ ≫ q)
    {N M : Y.Modules} (u : Γ(P, ⊤))
    (σ : (Scheme.Modules.pullback p₁).obj ((Scheme.Modules.pullback q).obj M) ⟶
      (Scheme.Modules.pullback p₁).obj ((Scheme.Modules.pullback q).obj M))
    (hσ : ∀ (U : P.Opens) (s : Γ((Scheme.Modules.pullback p₁).obj ((Scheme.Modules.pullback q).obj M), U)),
      σ.app U s = (P.presheaf.map (homOfLE (le_top (a := U))).op u) • s)
    (β : (Scheme.Modules.pullback q).obj N ≅ (Scheme.Modules.pullback q).obj M)
    (hβ : (Scheme.Modules.pullback p₁).map β.hom ≫
        (σ ≫ ((Scheme.Modules.pullbackComp p₁ q).hom.app M ≫
          eqToHom (show (Scheme.Modules.pullback (p₁ ≫ q)).obj M = (Scheme.Modules.pullback (p₂ ≫ q)).obj M by
            rw [hp]) ≫
          (Scheme.Modules.pullbackComp p₂ q).inv.app M)) =
      ((Scheme.Modules.pullbackComp p₁ q).hom.app N ≫
          eqToHom (show (Scheme.Modules.pullback (p₁ ≫ q)).obj N = (Scheme.Modules.pullback (p₂ ≫ q)).obj N by
            rw [hp]) ≫
          (Scheme.Modules.pullbackComp p₂ q).inv.app N) ≫ (Scheme.Modules.pullback p₂).map β.hom)
    (f' : X' ⟶ Spec (CommRingCat.of R')) {T' : X' ⟶ X'} {q' : X' ⟶ Y'} (h' : T' ≫ q' = q') (hT' : T' ≫ f' = f')
    (gX : X' ⟶ X) (gY : Y' ⟶ Y) (hq : gX ≫ q = q' ≫ gY)
    (s : X' ⟶ P) (hs₁ : s ≫ p₁ = gX) (hs₂ : s ≫ p₂ = T' ≫ gX)
    (c : R') (hsu : s.appTop u = f'.appTop ((Scheme.ΓSpecIso (CommRingCat.of R')).inv c)) :
    HasValue f' h'
      ((Scheme.Modules.pullbackComp q' gY).app N ≪≫ (Scheme.Modules.pullbackCongr hq.symm).app N ≪≫
        ((Scheme.Modules.pullbackComp gX q).app N).symm ≪≫ (Scheme.Modules.pullback gX).mapIso β ≪≫
        (Scheme.Modules.pullbackComp gX q).app M ≪≫ (Scheme.Modules.pullbackCongr hq).app M ≪≫
        ((Scheme.Modules.pullbackComp q' gY).app M).symm)
      c := by sorry
