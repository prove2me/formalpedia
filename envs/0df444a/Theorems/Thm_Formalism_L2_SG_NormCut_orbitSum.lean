-- Prove2me | Theorems.Thm_Formalism_L2_SG_NormCut_orbitSum
-- name    : Formalism.L2.SG.NormCut.orbitSum
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:47:13.018528+00:00
-- url     : https://prove2.me/theorems/e0a250aa-6fa0-4895-87ca-3c65a62184b7
-- title:
--   Norm Cut: orbit Sum
-- statement:
--   The Norm Cut construction uses the orbit Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/NormCore.lean#L38-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/NormCore.lean#L38-L49

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

theorem Formalism.L2.SG.NormCut.orbitSum {G C : Type*} [Group G] [Fintype G] [Fintype C] (A U : Set G) (s : C → G)
    (hb : Function.Bijective (fun x : A × C × U => (x.1 : G) * s x.2.1 * (x.2.2 : G))) (f : G → ℂ)
    (hf : ∀ x, ∀ a ∈ A, ∀ w ∈ U, f (a * x * w) = f x) :
    ∑ x : G, f x = (Nat.card A : ℂ) * (Nat.card U : ℂ) * ∑ c : C, f (s c) := by sorry
