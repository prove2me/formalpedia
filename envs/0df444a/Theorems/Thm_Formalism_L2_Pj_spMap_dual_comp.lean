-- Prove2me | Theorems.Thm_Formalism_L2_Pj_spMap_dual_comp
-- name    : Formalism.L2.Pj.spMap_dual_comp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:00:37.436457+00:00
-- url     : https://prove2.me/theorems/d4ffd781-5033-477a-b557-6b3319b49e70
-- title:
--   Pj: sp Map dual comp
-- statement:
--   The Pj construction uses the sp Map dual comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/FrameCharts.lean#L122-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/FrameCharts.lean#L122-L127

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

theorem Formalism.L2.Pj.spMap_dual_comp {K : Type} [Field K] {S T U : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T]
    [CommRing U] [Algebra K U] (φ : S →ₐ[K] T) (ψ : T →ₐ[K] U) :
    spMap (dualMap (ψ.comp φ).toRingHom) = spMap (dualMap ψ.toRingHom) ≫ spMap (dualMap φ.toRingHom) := by sorry
