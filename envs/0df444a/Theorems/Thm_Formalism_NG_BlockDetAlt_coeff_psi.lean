-- Prove2me | Theorems.Thm_Formalism_NG_BlockDetAlt_coeff_psi
-- name    : Formalism.NG.BlockDetAlt.coeff_psi
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:12:09.57228+00:00
-- url     : https://prove2.me/theorems/01513d30-4cb2-4881-aa30-d4062f13f394
-- title:
--   Block Det Alt: coeff psi
-- statement:
--   The Block Det Alt construction uses the coeff psi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/IsUnitDetOfConst.lean#L129-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/IsUnitDetOfConst.lean#L129-L166

import Definitions.Def_Formalism_CharacterColumnKernels_StatementN
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_IsUnitDetOfConst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.NG
open Formalism.NG.BlockDetAlt
variable {O : Type*} [CommRing O] {X' : Type*}
variable {d : Type} [Fintype d] [DecidableEq d]
variable {K : Type*} [CommRing K]

theorem Formalism.NG.BlockDetAlt.coeff_psi (m : ℕ) (P : MvPolynomial (Fin m) K) :
    PowerSeries.coeff m (psi m P) =
      ∑ e ∈ Finset.Iic (bnd m), if wt e = m then MvPolynomial.coeff e P else 0 := by sorry
