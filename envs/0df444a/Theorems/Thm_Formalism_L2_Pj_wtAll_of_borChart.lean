-- Prove2me | Theorems.Thm_Formalism_L2_Pj_wtAll_of_borChart
-- name    : Formalism.L2.Pj.wtAll_of_borChart
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:10.398062+00:00
-- url     : https://prove2.me/theorems/48b58fba-8cf3-47e9-9f31-0f1812caeadf
-- title:
--   Pj: wt All of bor Chart
-- statement:
--   The Pj construction uses the wt All of bor Chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ChartWD.lean#L77-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ChartWD.lean#L77-L95

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AlgebraMapCAt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ChartWD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
variable {K : Type} [Field K] {ι : Type}
variable (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
variable (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
  (S →ₐ[K] T) → pts S → pts T → Prop)
variable (borR : ∀ {S : Type} [CommRing S] [Algebra K S], (ι → Sˣ) → pts S → pts S → Prop)
variable {pts mapR borR}

theorem Formalism.L2.Pj.wtAll_of_borChart [Fintype ι] (h : BorChart pts mapR borR) (e : ι → ℕ) {f : Rules pts}
    (hf : IsNatural pts mapR f) (hw : IsWeight pts borR e f) (S : Type) [CommRing S] [Algebra K S] (t : ι → Sˣ)
    (y y' : pts S) (hy : FromTest pts mapR y) (hy' : FromTest pts mapR y') (hb : borR t y y') :
    evalAt pts mapR f y' = wchar e t * evalAt pts mapR f y := by sorry
