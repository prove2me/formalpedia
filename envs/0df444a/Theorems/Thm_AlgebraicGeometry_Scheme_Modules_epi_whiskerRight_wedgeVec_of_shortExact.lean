-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_epi_whiskerRight_wedgeVec_of_shortExact
-- name    : AlgebraicGeometry.Scheme.Modules.epi_whiskerRight_wedgeVec_of_shortExact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/c3b9c27e-e7e4-517c-a6cf-7401736e9dc5
-- title:
--   Epimorphy of bigwedgeⁿE'otimesE→bigwedgeⁿ⁺¹E
-- statement:
--   Let $X$ be a scheme and let $S$ be a short complex $S_1 \xrightarrow{f} S_2 \xrightarrow{g} S_3$ in the category `X.Modules` of sheaves of $\mathcal O_X$-modules, assumed to be short exact (so $f$ is a monomorphism, $g$ an epimorphism, and the complex is exact in the middle). Assume $S_1$ is locally free of rank $n$ in the sense of `IsLocallyFreeOfRank`, i.e. every point of $X$ has an open neighbourhood $U$ for which the pullback of $S_1$ along the inclusion $U \to X$ is isomorphic to the free sheaf of modules on a set of cardinality $n$; and assume $S_3$ is invertible in the sense of `IsInvertible`, i.e. every point has an open neighbourhood $U$ for which the pullback of $S_3$ along $U \to X$ is isomorphic to the unit sheaf of modules on $U$. Here the $n$-th exterior power functor on `X.Modules` is the sheafification of the presheaf-level exterior power, and `wedgeVec n M` is the morphism $\bigwedge^n M \otimes M \to \bigwedge^{n+1} M$ obtained by sheafifying the presheaf map given on sections by $\xi \otimes m \mapsto \xi \wedge m$. The conclusion is that the composite of $\bigl(\bigwedge^n f\bigr) \otimes \mathrm{id}_{S_2}$, i.e. `(exteriorPower X n).map S.f ▷ S.X₂`, followed by `wedgeVec n S.X₂`, is an epimorphism of sheaves of $\mathcal O_X$-modules.
--
--   This is the local computation underlying the multiplicativity of the determinant on short exact sequences of vector bundles: for $0 \to \mathcal E' \to \mathcal E \to \mathcal L \to 0$ with $\mathcal E'$ locally free of rank $n$ and $\mathcal L$ invertible, the map $\bigwedge^n \mathcal E' \otimes \mathcal E \to \bigwedge^{n+1}\mathcal E$ is surjective. It is used to produce the isomorphism $\det^{n+1} \mathcal E \cong \det^n \mathcal E' \otimes \mathcal L$ asserted by `nonempty_det_succ_iso_det_tensor_of_shortExact`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_epi_whiskerRight_wedgeVec_of_shortExact.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesDet
import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesWedge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory

theorem AlgebraicGeometry.Scheme.Modules.epi_whiskerRight_wedgeVec_of_shortExact
    {X : Scheme.{u}} {n : ℕ} (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (h₁ : Scheme.Modules.IsLocallyFreeOfRank n S.X₁) (h₃ : Scheme.Modules.IsInvertible S.X₃) :
    Epi (((Scheme.Modules.exteriorPower X n).map S.f ▷ S.X₂) ≫ Scheme.Modules.wedgeVec n S.X₂) := by sorry
