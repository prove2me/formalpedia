-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_eq_sum_smul_pullbackSection_of_subsingleton_HSucc
-- name    : AlgebraicGeometry.Scheme.Modules.exists_eq_sum_smul_pullbackSection_of_subsingleton_HSucc
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/4b606792-a32b-56d8-954a-eb28d2d3b336
-- title:
--   Base change of global sections at a field-valued point
-- statement:
--   Let $R$ be a Noetherian commutative ring, $X$ a scheme and $f\colon X\to\operatorname{Spec}R$ a proper flat morphism. Let $M$ be a sheaf of modules on $X$ which is invertible in the sense that every point of $X$ has an open neighbourhood $U$ such that the pullback of $M$ along the inclusion $U\hookrightarrow X$ is isomorphic to the unit sheaf of $U$. Assume that for every ordered affine cover $\mathcal U$ of $X$ (a finite family of affine opens, indexed by a linearly ordered finite type, with supremum $\top$) the $\mathcal O$-module presheaf $U\mapsto\Gamma(M,U)$ attached to $f$ is Čech-finite on $\mathcal U$: its degree-zero cohomology and each quotient $\ker d^{i+1}/\operatorname{im} d^{i}$ are finite $R$-modules. Let $K$ be a field with an $R$-algebra structure, write $X_K=X\times_{\operatorname{Spec}R}\operatorname{Spec}K$ with projections $p=\operatorname{pullback.fst}$ to $X$ and $q=\operatorname{pullback.snd}$ to $\operatorname{Spec}K$, and assume that for every ordered affine cover $\mathcal W$ of $X_K$ the group $\ker d^{1}/\operatorname{im} d^{0}$ of the Čech complex of $p^{*}M$ on $\mathcal W$ is a subsingleton. Then for every $k$ and every family $\tau\colon\mathrm{Fin}\,k\to\Gamma(p^{*}M,\top)$ there exist $N$, global sections $m_0,\dots,m_N\in\Gamma(M,\top)$ and scalars $c_{ij}\in K$ such that each $\tau_i=\sum_{j} c_{ij}\cdot p^{*}(m_j)$, where $c_{ij}$ acts through its image as a global function on $X_K$ under $q$ and $p^{*}(m_j)$ denotes the image of $m_j$ under the unit of the pullback–pushforward adjunction for $p$, evaluated on $\top$.
--
--   This is cohomology and base change in degree $0$ at a single field-valued point, in its surjective form: the canonical map $K\otimes_R\Gamma(X,M)\to\Gamma(X_K,p^{*}M)$ hits any prescribed finite family of sections on the fibre. It is used in the study of invertible modules on proper flat families, where finitely many sections over a geometric fibre must be realised from global sections of the family.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_eq_sum_smul_pullbackSection_of_subsingleton_HSucc.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.Scheme.Modules.exists_eq_sum_smul_pullbackSection_of_subsingleton_HSucc
    (R : Type u) [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [IsProper f] [Flat f] (M : X.Modules) (hM : Scheme.Modules.IsInvertible M)
    (hfin : ∀ 𝒰 : X.OrderedAffineCover, (OModulePresheaf.ofModules f M).CechFinite 𝒰)
    (K : Type u) [Field K] [Algebra R K]
    (hH1 : ∀ 𝒲 : (Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K)))).OrderedAffineCover,
      Subsingleton
        ((OModulePresheaf.ofModules (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))))
            ((Scheme.Modules.pullback
                (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))))).obj M)).HSucc 𝒲 0))
    {k : ℕ} (τ : Fin k → Γ((Scheme.Modules.pullback
        (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))))).obj M, ⊤)) :
    ∃ (N : ℕ) (m : Fin (N + 1) → Γ(M, ⊤)) (c : Fin k → Fin (N + 1) → K), ∀ i,
      τ i = ∑ j, ((Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))).appTop
                    ((Scheme.ΓSpecIso (.of K)).inv (c i j))) •
        (show Γ((Scheme.Modules.pullback
                  (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))))).obj M, ⊤) from
          (((Scheme.Modules.pullbackPushforwardAdjunction
            (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))))).unit.app M).app ⊤) (m j)) := by sorry
