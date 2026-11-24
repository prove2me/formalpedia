-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1_li_of_lead
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1.li_of_lead
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:35:45.723581+00:00
-- url     : https://prove2.me/theorems/57a2975b-ec9a-4da9-a5b4-0b3324756abc
-- title:
--   A1: li of lead
-- statement:
--   The A1 construction uses the li of lead property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/IsWeightedHomogeneousZeroStripPathWord.lean#L643-L671
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/IsWeightedHomogeneousZeroStripPathWord.lean#L643-L671

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IsWeightedHomogeneousZeroStripPathWord
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1.li_of_lead {k V V' ι O : Type*} [Field k] [AddCommGroup V] [Module k V] [AddCommGroup V']
    [Module k V'] [LinearOrder O] (v : ι → V) (Γ : ι → O) (π : O → V →ₗ[k] V')
    (h0 : ∀ i γ, Γ i < γ → π γ (v i) = 0)
    (hli : ∀ γ, LinearIndependent k (fun i : {i // Γ i = γ} => π γ (v i.1))) :
    LinearIndependent k v := by sorry
