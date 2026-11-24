-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z0_LF_loc_le_of_denom
-- name    : Formalism.L2.SG.Pf.LatDictZ.Z0.LF.loc_le_of_denom
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T16:58:22.148795+00:00
-- url     : https://prove2.me/theorems/9d3a029f-a5ac-4247-aca6-6fe8debe7b39
-- title:
--   LF: loc le of denom
-- statement:
--   The LF construction uses the loc le of denom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SelfDualUnimodular/LocalLatticeDictionary/LocFin.lean#L57-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SelfDualUnimodular/LocalLatticeDictionary/LocFin.lean#L57-L65

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZAbs
import Definitions.Def_Lemmata_Denominators_Denom
import Definitions.Def_Formalism_SelfDualUnimodular_LocalLatticeDictionary_LocFin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDictZ Formalism.L2.SG.Pf.LatDictZ.Z0 Formalism.L2.SG.Pf.LatDictZ.Z0.LF
open ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA
variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem Formalism.L2.SG.Pf.LatDictZ.Z0.LF.loc_le_of_denom {L M : Submodule (𝓞 E) (Fin n → E)} {N : ℕ} (hN : ∀ x ∈ L, (N : 𝓞 E) • x ∈ M)
    {p : Ideal (𝓞 E)} (hp : p.IsPrime) (hNp : (N : 𝓞 E) ∉ p) :
    Formalism.HermitianLatticesTheory.loc (K := E) p L ≤ Formalism.HermitianLatticesTheory.loc (K := E) p M := by sorry
