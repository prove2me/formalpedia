-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_eq_sum_smul_pullbackSection_of_isReduced_of_finrank_eq
-- name    : AlgebraicGeometry.Scheme.Modules.exists_eq_sum_smul_pullbackSection_of_isReduced_of_finrank_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/099d5a81-3acf-5301-a7ac-be0731e76f8d
-- title:
--   Degree-zero base change over a reduced base with constant h⁰
-- statement:
--   Let $R$ be a reduced Noetherian commutative ring, $X$ a scheme, $f\colon X\to\operatorname{Spec}R$ a proper flat morphism, and $M$ a sheaf of $\mathcal O_X$-modules. Assume $M$ is Zariski-locally trivial: every point of $X$ has an open neighbourhood $U$ for which the pullback of $M$ along the inclusion $U\hookrightarrow X$ is isomorphic to the unit sheaf of modules on $U$. Let $r$ be a natural number and assume that for every prime $\mathfrak p$ of $R$ the space of global sections of the pullback of $M$ along the first projection $X\times_{\operatorname{Spec}R}\operatorname{Spec}\kappa(\mathfrak p)\to X$, viewed as a $\kappa(\mathfrak p)$-module through the second projection (scalars acting via $\kappa(\mathfrak p)\to\Gamma$ of the structure sheaf), has rank exactly $r$. Let $A$ be an $R$-algebra, write $p_A$ for the first projection $X\times_{\operatorname{Spec}R}\operatorname{Spec}A\to X$, and let $\tau_0,\dots,\tau_{k-1}$ be finitely many global sections of $p_A^{*}M$. Then there exist $N\in\mathbb N$, global sections $m_0,\dots,m_N$ of $M$ on $X$ and scalars $c_{ij}\in A$ such that each $\tau_i=\sum_{j}c_{ij}\cdot p_A^{*}m_j$, where $c_{ij}$ acts through $A\cong\Gamma(\operatorname{Spec}A,\mathcal O)\to\Gamma(X_A,\mathcal O_{X_A})$ and $p_A^{*}m_j$ denotes the image of $m_j$ under the unit of the pullback–pushforward adjunction, evaluated on global sections.
--
--   This is the sections-level form of cohomology and base change in degree $0$ over a reduced Noetherian base with constant fibrewise $h^0$: applied to a single section it says that $A\otimes_R\Gamma(X,M)\to\Gamma(X_A,p_A^{*}M)$ is surjective. It is used in the seesaw-type argument, being cited by [`AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_bijective_smul_of_le_preimage_basicOpen_of_forall_isMaximal`](thm.html#AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_bijective_smul_of_le_preimage_basicOpen_of_forall_isMaximal).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_eq_sum_smul_pullbackSection_of_isReduced_of_finrank_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.exists_eq_sum_smul_pullbackSection_of_isReduced_of_finrank_eq
    {R : Type u} [CommRing R] [IsNoetherianRing R] [_root_.IsReduced R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] (M : X.Modules)
    (htriv : ∀ x : X, ∃ (U : X.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf))
    (r : ℕ)
    (hconst : ∀ 𝔭 : PrimeSpectrum R,
      letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom
        (Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap R 𝔭.asIdeal.ResidueField))
        ((Scheme.Modules.pullback
          (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R 𝔭.asIdeal.ResidueField))).obj M) ⊤
      Module.finrank 𝔭.asIdeal.ResidueField
        Γ((Scheme.Modules.pullback
          (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R 𝔭.asIdeal.ResidueField))).obj M, ⊤) = r)
    (A : Type u) [CommRing A] [Algebra R A]
    {k : ℕ} (τ : Fin k → Γ((Scheme.Modules.pullback
        (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A))).obj M, ⊤)) :
    ∃ (N : ℕ) (m : Fin (N + 1) → Γ(M, ⊤)) (c : Fin k → Fin (N + 1) → A), ∀ i,
      τ i = ∑ j, ((Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap R A)).appTop
                    ((Scheme.ΓSpecIso (.of A)).inv (c i j))) •
        (show Γ((Scheme.Modules.pullback
                  (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A))).obj M, ⊤) from
          (((Scheme.Modules.pullbackPushforwardAdjunction
            (Limits.pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A))).unit.app M).app ⊤) (m j)) := by sorry
