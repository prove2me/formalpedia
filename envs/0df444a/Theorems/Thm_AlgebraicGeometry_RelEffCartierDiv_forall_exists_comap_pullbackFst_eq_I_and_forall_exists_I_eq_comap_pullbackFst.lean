-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_forall_exists_comap_pullbackFst_eq_I_and_forall_exists_I_eq_comap_pullbackFst
-- name    : AlgebraicGeometry.RelEffCartierDiv.forall_exists_comap_pullbackFst_eq_I_and_forall_exists_I_eq_comap_pullbackFst
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/7916ccc5-5504-573e-813a-da7e1b027072
-- title:
--   Relative effective divisors transport along the base-change isomorphism
-- statement:
--   Let $f\colon\mathcal C\to S$ and $g\colon T\to S$ be morphisms of schemes and let $r$ be a natural number. Write $p=\mathrm{pr}_2\colon \mathcal C\times_S T\to T$ for the second projection and $e=\mathrm{pr}_1\colon (\mathcal C\times_S T)\times_T T\to \mathcal C\times_S T$ for the first projection of the pullback of $p$ along $\mathrm{id}_T$. Here a term of `RelEffCartierDiv f r g` consists of an ideal sheaf datum $I$ on $\mathcal C\times_S T$ such that the inclusion of the associated closed subscheme followed by $\mathrm{pr}_2\colon\mathcal C\times_S T\to T$ is finite, flat and locally of finite presentation, and has fibrewise rank equal to $r$ at every point $t$ of $T$; similarly `RelEffCartierDiv p r (𝟙 T)` consists of such data on $(\mathcal C\times_S T)\times_T T$ relative to $\mathrm{pr}_2\colon (\mathcal C\times_S T)\times_T T\to T$. The assertion is the conjunction of two statements: first, for every $D'$ of the second kind there is a $D$ of the first kind with $e^{*}(D.I)=D'.I$ (comap of ideal sheaf data along $e$); second, for every $D$ of the first kind there is a $D'$ of the second kind with $D'.I=e^{*}(D.I)$. No hypotheses beyond the data are imposed.
--
--   This is the translation between the two bookkeeping conventions for a relative effective divisor of degree $r$: as a divisor for the family $f$ at the $S$-point $g$, or as a divisor for the base-changed family $\mathcal C\times_S T\to T$ at the identity point of $T$. It is used in the study of the modular curve $X_1$, where results about divisors on fibres of a smooth proper family are applied after base change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelEffCartierDiv_forall_exists_comap_pullbackFst_eq_I_and_forall_exists_I_eq_comap_pullbackFst.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicCurve_RelCartier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.RelEffCartierDiv.forall_exists_comap_pullbackFst_eq_I_and_forall_exists_I_eq_comap_pullbackFst
    {𝒞 S T : Scheme.{u}} (f : 𝒞 ⟶ S) (g : T ⟶ S) (r : ℕ) :
    (∀ D' : RelEffCartierDiv (pullback.snd f g) r (𝟙 T),
        ∃ D : RelEffCartierDiv f r g, D.I.comap (pullback.fst (pullback.snd f g) (𝟙 T)) = D'.I) ∧
    (∀ D : RelEffCartierDiv f r g,
        ∃ D' : RelEffCartierDiv (pullback.snd f g) r (𝟙 T), D'.I = D.I.comap (pullback.fst (pullback.snd f g) (𝟙 T))) := by sorry
