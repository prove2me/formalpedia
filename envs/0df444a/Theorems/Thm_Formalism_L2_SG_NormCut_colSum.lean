-- Prove2me | Theorems.Thm_Formalism_L2_SG_NormCut_colSum
-- name    : Formalism.L2.SG.NormCut.colSum
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:46:51.695219+00:00
-- url     : https://prove2.me/theorems/18a647bd-75d1-56ab-8c04-649ef4fdcdd2
-- title:
--   Norm Cut: col Sum
-- statement:
--   The Norm Cut construction uses the col Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/NormCore.lean#L12-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/NormCore.lean#L12-L36

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_NormCore
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.NormCut

theorem Formalism.L2.SG.NormCut.colSum {G : Type*} [Group G] [Fintype G] (U : Set G) (p : G → ℂ) (h0 : ∀ x, x ∉ U → p x = 0)
    (hr : ∀ x, ∀ w ∈ U, p (x * w) = p x * p w) (hn : ∀ w ∈ U, conj (p w) * p w = 1) (i j : G) :
    ∑ s : G, ∑ s' : G, conj (p (s⁻¹ * i * s')) * p (s⁻¹ * j * s') =
      (Nat.card U : ℂ) * ∑ s : G, conj (p (s⁻¹ * (i * j⁻¹) * s)) := by sorry
