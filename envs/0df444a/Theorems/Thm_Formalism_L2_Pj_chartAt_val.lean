-- Prove2me | Theorems.Thm_Formalism_L2_Pj_chartAt_val
-- name    : Formalism.L2.Pj.chartAt_val
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:56:48.546249+00:00
-- url     : https://prove2.me/theorems/c5fb4369-5546-4d43-b099-332a2012fe7a
-- title:
--   Pj: chart At val
-- statement:
--   The Pj construction uses the chart At val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ChartWD.lean#L39-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ChartWD.lean#L39-L50

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

theorem Formalism.L2.Pj.chartAt_val {f : Rules pts} (hf : IsNatural pts mapR f) {S : Type} [CommRing S] [Algebra K S] {w : pts S}
    {m : Ideal S} [m.IsPrime] {A : TRing K} {u : pts A.R} {c : A.R →ₐ[K] Localization.AtPrime m}
    (hc : FrChartAt pts mapR w m A u c) {p : TRing K} {φ : p.R →ₐ[K] S} {y : pts p.R} (hy : mapR φ y w) :
    locM K m (φ (f p y)) = c (f A u) := by sorry
