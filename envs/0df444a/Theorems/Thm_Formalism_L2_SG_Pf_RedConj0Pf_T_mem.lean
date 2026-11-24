-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_RedConj0Pf_T_mem
-- name    : Formalism.L2.SG.Pf.RedConj0Pf.T_mem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:43:07.794103+00:00
-- url     : https://prove2.me/theorems/d3a68c8c-b238-496a-b7a1-f59318f73968
-- title:
--   Red Conj0 Pf: T mem
-- statement:
--   The Red Conj0 Pf construction uses the T mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/ReductionConjugacy.lean#L28-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/ReductionConjugacy.lean#L28-L47

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

theorem Formalism.L2.SG.Pf.RedConj0Pf.T_mem {p : ℕ} {x : I.Gf} {M : Matrix (Fin I.n) (Fin I.n) (ZMod p)} {b : Fin I.n → (Fin I.n → I.E)}
    (hb : ∀ i, b i ∈ I.L)
    (hM : ∀ i, I.fmat x *ᵥ iv I (b i) - ∑ j, (((M j i).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b j) ∈ Lw I w)
    (i : Fin I.n) : I.fmat x *ᵥ iv I (b i) ∈ I.Lf := by sorry
