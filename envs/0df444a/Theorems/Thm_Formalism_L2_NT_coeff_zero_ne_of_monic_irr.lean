-- Prove2me | Theorems.Thm_Formalism_L2_NT_coeff_zero_ne_of_monic_irr
-- name    : Formalism.L2.NT.coeff_zero_ne_of_monic_irr
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:09:27.780509+00:00
-- url     : https://prove2.me/theorems/7a91c135-f112-4a1d-948a-f3b1658be81c
-- title:
--   NT: coeff zero ne of monic irr
-- statement:
--   The NT construction uses the coeff zero ne of monic irr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoeffZeroNeOfMonicIrr.lean#L37-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoeffZeroNeOfMonicIrr.lean#L37-L45

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisConjCentralIdempotent
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_TypesDefs
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoeffZeroNeOfMonicIrr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Formalism.IrreducibleCountingLemmas.TYPES CategoryTheory
open Formalism Formalism.L2 Formalism.L2.NT
variable {g : ℕ} [Fact g.Prime]

theorem Formalism.L2.NT.coeff_zero_ne_of_monic_irr {K : Type} [Field K] {P : K[X]} (hm : P.Monic) (hi : Irreducible P) (hX : P ≠ X) :
    P.coeff 0 ≠ 0 := by sorry
