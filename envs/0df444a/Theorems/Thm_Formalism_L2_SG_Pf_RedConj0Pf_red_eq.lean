-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_RedConj0Pf_red_eq
-- name    : Formalism.L2.SG.Pf.RedConj0Pf.red_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:42:51.403712+00:00
-- url     : https://prove2.me/theorems/cd9730df-4dff-4e5d-8290-f2dc886bced9
-- title:
--   Red Conj0 Pf: red eq
-- statement:
--   The Red Conj0 Pf construction uses the red eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/ReductionConjugacy.lean#L49-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/ReductionConjugacy.lean#L49-L59

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

theorem Formalism.L2.SG.Pf.RedConj0Pf.red_eq {p : ℕ} {x : I.Gf} {M : Matrix (Fin I.n) (Fin I.n) (ZMod p)} {b : Fin I.n → (Fin I.n → I.E)}
    (hM : ∀ i, I.fmat x *ᵥ iv I (b i) - ∑ j, (((M j i).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b j) ∈ Lw I w)
    (i : Fin I.n) : (Lw I w).mkQ (I.fmat x *ᵥ iv I (b i)) =
      ∑ j, (((M j i).val : ℕ) : ℤ) • (Lw I w).mkQ (iv I (b j)) := by sorry
