-- Prove2me | Theorems.Thm_Formalism_L2_Pj_chartAt_of_cover
-- name    : Formalism.L2.Pj.chartAt_of_cover
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:59:32.486823+00:00
-- url     : https://prove2.me/theorems/dd8d350c-c4e3-468a-ba63-4c39abdafce3
-- title:
--   Pj: chart At of cover
-- statement:
--   The Pj construction uses the chart At of cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/FrameCharts.lean#L59-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/FrameCharts.lean#L59-L74

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
variable {K : Type} [Field K] {ι : Type}
variable (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
variable (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
  (S →ₐ[K] T) → pts S → pts T → Prop)
variable (borR : ∀ {S : Type} [CommRing S] [Algebra K S], (ι → Sˣ) → pts S → pts S → Prop)
variable {pts mapR borR}

theorem Formalism.L2.Pj.chartAt_of_cover (hT : MapTrans pts mapR) (hC : MapCancel pts mapR) {S : Type} [CommRing S] [Algebra K S]
    {w : pts S} {m : Ideal S} [m.IsPrime] {A : TRing K} {u : pts A.R} {c : A.R →ₐ[K] Localization.AtPrime m}
    (hu : IsMonoPt pts mapR u) (hcl : ChartCls pts mapR w m u c) (hloc : ChartLoc pts mapR w m A u) :
    FrChartAt pts mapR w m A u c := by sorry
