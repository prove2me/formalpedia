-- Prove2me | Theorems.Thm_Formalism_L2_Pj_spMap_algHom_comp
-- name    : Formalism.L2.Pj.spMap_algHom_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:00:05.836807+00:00
-- url     : https://prove2.me/theorems/24db3248-589b-4acd-8e8f-d7c2b3b1ec49
-- title:
--   Pj: sp Map alg Hom comp
-- statement:
--   The Pj construction uses the sp Map alg Hom comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/FrameCharts.lean#L111-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/FrameCharts.lean#L111-L115

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnitIndepOfCharts
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem Formalism.L2.Pj.spMap_algHom_comp {K : Type} [Field K] {S T U : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T]
    [CommRing U] [Algebra K U] (φ : S →ₐ[K] T) (ψ : T →ₐ[K] U) :
    spMap (ψ.comp φ).toRingHom = spMap ψ.toRingHom ≫ spMap φ.toRingHom := by sorry
