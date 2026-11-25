-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_UpFBr_Pl_mem_pow_iff
-- name    : Formalism.L2.FormalSeriesBounds.UpFBr.Pl.mem_pow_iff
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:28:34.932462+00:00
-- url     : https://prove2.me/theorems/74b6b409-84dc-4357-900a-59598f75afc1
-- title:
--   Pl: mem pow iff
-- statement:
--   The Pl construction uses the mem pow iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CompleteOfBasis.lean#L17-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CompleteOfBasis.lean#L17-L31

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieUpFBrPl
import Definitions.Def_Lemmata_MiscLemmasH_Imports
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CompleteOfBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open TensorProduct IsLocalRing Polynomial
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.UpFBr Formalism.L2.FormalSeriesBounds.UpFBr.Pl
variable {Z : Type} [CommRing Z] (π : Z) {A : Type} [CommRing A] [Algebra Z A] {N : ℕ}
  (β : Module.Basis (Fin N) Z A)

theorem Formalism.L2.FormalSeriesBounds.UpFBr.Pl.mem_pow_iff (n : ℕ) (x : A) :
    x ∈ ((Ideal.span {algebraMap Z A π}) ^ n • (⊤ : Submodule A A)) ↔
      ∀ i, β.repr x i ∈ ((Ideal.span {π}) ^ n • (⊤ : Submodule Z Z)) := by sorry
