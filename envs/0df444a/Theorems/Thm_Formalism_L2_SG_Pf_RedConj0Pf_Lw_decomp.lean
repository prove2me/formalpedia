-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_RedConj0Pf_Lw_decomp
-- name    : Formalism.L2.SG.Pf.RedConj0Pf.Lw_decomp
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:28:18.3138+00:00
-- url     : https://prove2.me/theorems/51395255-3024-4f32-899f-0398a6e94cce
-- title:
--   Red Conj0 Pf: Lw decomp
-- statement:
--   The Red Conj0 Pf construction uses the Lw decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/MemWLat0OfIv.lean#L55-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/MemWLat0OfIv.lean#L55-L83

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

theorem Formalism.L2.SG.Pf.RedConj0Pf.Lw_decomp (p : ℕ) (hp0 : 0 < p) {z : Fin I.n → I.E ⊗[I.F] Af I.F} (hz : z ∈ Lw I w) :
    ∃ l ∈ wLat0 I w, ∃ y ∈ I.Lf, z = iv I l + (p : I.E ⊗[I.F] Af I.F) • y := by sorry
