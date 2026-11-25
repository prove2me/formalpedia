-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_RedConj0Pf_zcoef_A
-- name    : Formalism.L2.SG.Pf.RedConj0Pf.zcoef_A
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:42:31.955183+00:00
-- url     : https://prove2.me/theorems/3722d83b-3e71-4cdc-9af7-045246f9898e
-- title:
--   Red Conj0 Pf: zcoef A
-- statement:
--   The Red Conj0 Pf construction uses the zcoef A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/ReductionConjugacy.lean#L69-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/ReductionConjugacy.lean#L69-L76

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_MemWLat0OfIv
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_ReductionConjugacy
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

theorem Formalism.L2.SG.Pf.RedConj0Pf.zcoef_A (p : ℕ) (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p)
    {b : Fin I.n → (Fin I.n → I.E)} (hb : IsRedBasis0 I w b) (z : Fin I.n → ℤ)
    (hz : ∑ l, z l • (Lw I w).mkQ (iv I (b l)) = 0) (l : Fin I.n) : ((z l : ℤ) : ZMod p) = 0 := by sorry
