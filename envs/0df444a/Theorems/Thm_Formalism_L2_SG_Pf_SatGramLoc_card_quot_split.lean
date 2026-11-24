-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_SatGramLoc_card_quot_split
-- name    : Formalism.L2.SG.Pf.SatGramLoc.card_quot_split
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:47:12.155797+00:00
-- url     : https://prove2.me/theorems/b8e3ce9a-69a5-497b-b68f-8a3a4402aa51
-- title:
--   Sat Gram Loc: card quot split
-- statement:
--   The Sat Gram Loc construction uses the card quot split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/SatGramLocPfA.lean#L69-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/SatGramLocPfA.lean#L69-L82

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_SatGramLoc
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_SatGramLocPfA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.SatGramLoc
variable {K : Type} [Field K] [NumberField K]

theorem Formalism.L2.SG.Pf.SatGramLoc.card_quot_split (p : ℕ) (hp : p.Prime)
    (hs : {v : HeightOneSpectrum (𝓞 K) | ((p : ℕ) : 𝓞 K) ∈ v.asIdeal}.ncard = Module.finrank ℚ K)
    (v : HeightOneSpectrum (𝓞 K)) (hv : ((p : ℕ) : 𝓞 K) ∈ v.asIdeal) :
    Nat.card (𝓞 K ⧸ v.asIdeal) = p := by sorry
