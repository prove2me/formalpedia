-- Prove2me | Theorems.Thm_Formalism_L2_SG_NormCut_pairSum_gam
-- name    : Formalism.L2.SG.NormCut.pairSum_gam
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:56.59339+00:00
-- url     : https://prove2.me/theorems/881fbcee-bdb2-4d10-978f-83fb77d2ab23
-- title:
--   Norm Cut: pair Sum gam
-- statement:
--   The Norm Cut construction uses the pair Sum gam property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/NormAsm.lean#L25-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/NormAsm.lean#L25-L57

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_NormCore
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_NormAsm
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
variable {I : Type*} [Group I] [Fintype I]

theorem Formalism.L2.SG.NormCut.pairSum_gam (U : Set I) (p : I → ℂ) (h0 : ∀ x, x ∉ U → p x = 0)
    (hr : ∀ x, ∀ w ∈ U, p (x * w) = p x * p w) (hn : ∀ w ∈ U, conj (p w) * p w = 1)
    (hU : (Nat.card U : ℂ) ≠ 0) (i j : I) :
    ∑ s : I, ∑ s' : I, conj (p (s⁻¹ * i * s')) * p (s⁻¹ * j * s') =
      (Nat.card U : ℂ) ^ 2 * conj (gamOf U p (i * j⁻¹)) := by sorry
