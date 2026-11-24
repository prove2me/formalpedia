-- Prove2me | Theorems.Thm_Formalism_L2_Pj_borChart_of_cover
-- name    : Formalism.L2.Pj.borChart_of_cover
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:42:29.517334+00:00
-- url     : https://prove2.me/theorems/812c9c01-4497-469a-bb69-a2e882afb579
-- title:
--   Pj: bor Chart of cover
-- statement:
--   The Pj construction uses the bor Chart of cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/FrameCharts.lean#L85-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/FrameCharts.lean#L85-L103

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

theorem Formalism.L2.Pj.borChart_of_cover (hT : MapTrans pts mapR) (hC : MapCancel pts mapR) (hB : BorBC pts mapR borR)
    (h : ∀ (S : Type) [CommRing S] [Algebra K S] (t : ι → Sˣ) (w w' : pts S), borR t w w' →
      ∀ (m : Ideal S) [m.IsMaximal],
      ∃ (A : TRing K) (u : pts A.R) (c c' : A.R →ₐ[K] Localization.AtPrime m),
        IsMonoPt pts mapR u ∧ BorOver pts mapR borR A u ∧ ChartCls pts mapR w m u c ∧ ChartLoc pts mapR w m A u ∧
          ChartCls pts mapR w' m u c' ∧ ChartLoc pts mapR w' m A u) :
    BorChart pts mapR borR := by sorry
