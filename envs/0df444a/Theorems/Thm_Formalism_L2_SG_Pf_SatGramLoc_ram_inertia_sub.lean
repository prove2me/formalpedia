-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_SatGramLoc_ram_inertia_sub
-- name    : Formalism.L2.SG.Pf.SatGramLoc.ram_inertia_sub
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:56.854492+00:00
-- url     : https://prove2.me/theorems/c8037de1-fa65-4f00-8d89-fb6f3ad9681f
-- title:
--   Sat Gram Loc: ram inertia sub
-- statement:
--   The Sat Gram Loc construction uses the ram inertia sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/SatGramLocPfA.lean#L104-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/SatGramLocPfA.lean#L104-L127

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

theorem Formalism.L2.SG.Pf.SatGramLoc.ram_inertia_sub {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (p : ℕ) (hp : p.Prime)
    (hs : {w : HeightOneSpectrum (𝓞 E) | ((p : ℕ) : 𝓞 E) ∈ w.asIdeal}.ncard = Module.finrank ℚ E)
    (v : HeightOneSpectrum (𝓞 F)) (hv : ((p : ℕ) : 𝓞 F) ∈ v.asIdeal) :
    v.asIdeal.ramificationIdx ℤ = 1 ∧ v.asIdeal.inertiaDeg ℤ = 1 := by sorry
