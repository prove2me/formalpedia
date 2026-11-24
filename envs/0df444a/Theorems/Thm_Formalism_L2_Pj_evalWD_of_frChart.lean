-- Prove2me | Theorems.Thm_Formalism_L2_Pj_evalWD_of_frChart
-- name    : Formalism.L2.Pj.evalWD_of_frChart
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:37.742456+00:00
-- url     : https://prove2.me/theorems/8349b744-c3a1-4921-92e6-b68d9a2b8c5e
-- title:
--   Pj: eval WD of fr Chart
-- statement:
--   The Pj construction uses the eval WD of fr Chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ChartWD.lean#L62-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ChartWD.lean#L62-L68

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

theorem Formalism.L2.Pj.evalWD_of_frChart (h : FrChart pts mapR) : EvalWD pts mapR := by sorry
