-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_twoTermComplex_sectionsEquiv_forall_baseChange
-- name    : AlgebraicGeometry.Scheme.Modules.exists_twoTermComplex_sectionsEquiv_forall_baseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/cb00ff02-eeca-5f96-9d73-17edb542c338
-- title:
--   Degree-zero base change via a finite free two-term complex
-- statement:
--   Let $R$ be a Noetherian commutative ring, $X$ a scheme and $f \colon X \to \operatorname{Spec} R$ a proper flat morphism, and let $M$ be a sheaf of modules over the structure sheaf of $X$ which is Zariski-locally trivial, in the sense that every point of $X$ lies in an open $U$ for which the pullback of $M$ along the inclusion $U \hookrightarrow X$ is isomorphic to the unit sheaf of modules on $U$. Here $\Gamma(M,\top)$ is regarded as an $R$-module by restriction of scalars along the ring map $R \to \Gamma(X,\top)$ determined by $f$, and, for a commutative $R$-algebra $A$, the sections over the whole of $X_A = X \times_{\operatorname{Spec} R} \operatorname{Spec} A$ of the pullback $M_A$ of $M$ along the first projection are an $A$-module by restriction of scalars along the second projection $X_A \to \operatorname{Spec} A$. The assertion is that there exist a two-term complex $G$ over $R$, that is finite free $R$-modules $G^0$, $G^1$ together with an $R$-linear map $d \colon G^0 \to G^1$; an $R$-linear isomorphism $\varepsilon_0 \colon \Gamma(M,\top) \xrightarrow{\sim} \ker d$; and for every commutative $R$-algebra $A$ (in the same universe) an $A$-linear isomorphism $\varepsilon_A$ from $\Gamma(M_A, \top)$ onto `G.H0 A`, the kernel of the base change $d \otimes_R A \colon A \otimes_R G^0 \to A \otimes_R G^1$, subject to the single compatibility: for every such $A$ and every $m \in \Gamma(M,\top)$, the value of $\varepsilon_A$ at the image of $m$ under the unit of the pullback–pushforward adjunction for the first projection, taken at $M$ and at the top open, equals `G.kerBaseChangeHom A` applied to $1 \otimes \varepsilon_0(m)$, where that canonical comparison map $A \otimes_R \ker d \to \ker(d \otimes_R A)$ is the corestriction of the base change of the inclusion $\ker d \subseteq G^0$. No further conditions relating the $\varepsilon_A$ for different $A$ are imposed.
--
--   This is the degree-zero form of cohomology and base change for a proper flat morphism with locally trivial coefficient sheaf: the functor $A \mapsto \Gamma(X_A, M_A)$ on commutative $R$-algebras, together with its comparison maps out of $A \otimes_R \Gamma(X,M)$, is presented as the kernel functor of one fixed two-term complex of finite free $R$-modules. It is used in the study of invertible sheaves of modules, for the criteria [`AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_ideal_forall_locallyIsoOver_unit_iff_map_eq_bot`](thm.html#AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_ideal_forall_locallyIsoOver_unit_iff_map_eq_bot) and [`AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_nonempty_pullback_preimage_basicOpen_iso_unit_of_forall_sections_linearEquiv`](thm.html#AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_nonempty_pullback_preimage_basicOpen_iso_unit_of_forall_sections_linearEquiv), and for the behaviour of the geometric fibre rank [`AlgebraicGeometry.Scheme.Modules.geomFibreH0Finrank_comp_eq`](thm.html#AlgebraicGeometry.Scheme.Modules.geomFibreH0Finrank_comp_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_twoTermComplex_sectionsEquiv_forall_baseChange.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_CoherentBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.Scheme.Modules.exists_twoTermComplex_sectionsEquiv_forall_baseChange
    {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [IsProper f] [Flat f] (M : X.Modules)
    (htriv : ∀ x : X, ∃ (U : X.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)) :
    ∃ (G : CoherentBaseChange.TwoTermComplex.{u, u} R)
      (ε₀ : letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom f M ⊤
        Γ(M, ⊤) ≃ₗ[R] LinearMap.ker G.d)
      (ε : ∀ (A : Type u) [CommRing A] [Algebra R A],
        letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom
          (Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap R A))
          ((Scheme.Modules.pullback
            (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A))).obj M) ⊤
        Γ((Scheme.Modules.pullback
            (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A))).obj M, ⊤) ≃ₗ[A] G.H0 A),
      ∀ (A : Type u) [CommRing A] [Algebra R A] (m : Γ(M, ⊤)),
        ε A (show Γ((Scheme.Modules.pullback
                (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A))).obj M, ⊤) from
              (((Scheme.Modules.pullbackPushforwardAdjunction
                (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A))).unit.app M).app ⊤) m)
          = G.kerBaseChangeHom A (1 ⊗ₜ[R] ε₀ m) := by sorry
