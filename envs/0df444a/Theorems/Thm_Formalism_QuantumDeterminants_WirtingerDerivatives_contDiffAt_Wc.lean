-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_contDiffAt_Wc
-- name    : Formalism.QuantumDeterminants.WirtingerDerivatives.contDiffAt_Wc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:06:06.558065+00:00
-- url     : https://prove2.me/theorems/6fa1b4ce-1507-400f-ad1b-03ebb075e6fa
-- title:
--   Wirtinger Derivatives: cont Diff At Wc
-- statement:
--   The Wirtinger Derivatives construction uses the cont Diff At Wc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/WRWeyl.lean#L79-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/WRWeyl.lean#L79-L81

import Definitions.Def_Formalism_FormalDegreeBessel_StatementWR
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_WRWeyl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff Topology
open Filter
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.QuantumDeterminants.WirtingerDerivatives
variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.QuantumDeterminants.WirtingerDerivatives.contDiffAt_Wc {g : (Fin m → ℂ) → E} {x : Fin m → ℂ} (hg : ContDiffAt ℝ ∞ g x)
    (u w : Fin m → ℂ) (s : ℂ) : ContDiffAt ℝ ∞ (fun y => Wc u w s (fderiv ℝ g y)) x := by sorry
