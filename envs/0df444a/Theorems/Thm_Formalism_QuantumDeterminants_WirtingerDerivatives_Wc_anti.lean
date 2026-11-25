-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_Wc_anti
-- name    : Formalism.QuantumDeterminants.WirtingerDerivatives.Wc_anti
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:51:36.604128+00:00
-- url     : https://prove2.me/theorems/4dd58bb8-3484-4c19-acbb-99fe1a16068c
-- title:
--   Wirtinger Derivatives: Wc anti
-- statement:
--   The Wirtinger Derivatives construction uses the Wc anti property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/WRWeyl.lean#L138-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/WRWeyl.lean#L138-L148

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

theorem Formalism.QuantumDeterminants.WirtingerDerivatives.Wc_anti (k l : Fin m) (c : ℂ) (T : (Fin m → ℂ) →L[ℝ] ℂ) (hT : ∀ v, T v = c * star (v k)) :
    Wc (Pi.single l 1) (Pi.single l Complex.I) (-Complex.I) T = 0 ∧
      Wc (Pi.single l 1) (Pi.single l Complex.I) Complex.I T = (if l = k then c else 0) := by sorry
