-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_RedConj0Pf_mem_wLat0_of_iv
-- name    : Formalism.L2.SG.Pf.RedConj0Pf.mem_wLat0_of_iv
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:28:27.636875+00:00
-- url     : https://prove2.me/theorems/52010fbd-b5cd-4457-8067-bfda4b54bba6
-- title:
--   Red Conj0 Pf: mem w Lat0 of iv
-- statement:
--   The Red Conj0 Pf construction uses the mem w Lat0 of iv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/MemWLat0OfIv.lean#L85-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/MemWLat0OfIv.lean#L85-L108

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RowDictCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictAll
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_MemWLat0OfIv
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
open scoped TensorProduct Pointwise
open Matrix Formalism.MainNotions.S
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.RedConj0Pf
open Formalism.L2.SG.Pf.RowDictPf PIW.AdelClassFin
variable (I : AutInst) (w : IsDedekindDomain.HeightOneSpectrum (𝓞 I.E))

theorem Formalism.L2.SG.Pf.RedConj0Pf.mem_wLat0_of_iv (p : ℕ) (hp0 : 0 < p) (hpw : (p : 𝓞 I.E) ∈ w.asIdeal) (y : Fin I.n → I.E)
    (hy : iv I y ∈ Lw I w) : y ∈ wLat0 I w := by sorry
