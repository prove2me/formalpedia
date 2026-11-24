-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_RedConj0Pf_span_of_red
-- name    : Formalism.L2.SG.Pf.RedConj0Pf.span_of_red
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:28:24.893851+00:00
-- url     : https://prove2.me/theorems/f722ca7c-7955-4785-ac9c-6150beccfb67
-- title:
--   Red Conj0 Pf: span of red
-- statement:
--   The Red Conj0 Pf construction uses the span of red property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/MemWLat0OfIv.lean#L129-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/MemWLat0OfIv.lean#L129-L142

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

theorem Formalism.L2.SG.Pf.RedConj0Pf.span_of_red {m : ℕ} {b : Fin m → (Fin I.n → I.E)} (hb : IsRedBasis0 I w b) :
    I.L ≤ Submodule.span (𝓞 I.E) (Set.range b) ⊔ w.asIdeal • I.L := by sorry
