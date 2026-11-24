-- Prove2me | Theorems.Thm_Formalism_NG_BlockDetAlt_coeff_det_eq
-- name    : Formalism.NG.BlockDetAlt.coeff_det_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:12:26.652829+00:00
-- url     : https://prove2.me/theorems/e93d5d79-1bf2-4c3a-a6e1-c576157c5859
-- title:
--   Block Det Alt: coeff det eq
-- statement:
--   The Block Det Alt construction uses the coeff det eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/IsUnitDetOfConst.lean#L179-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/IsUnitDetOfConst.lean#L179-L218

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
variable {d : Type} [Fintype d] [DecidableEq d]

theorem Formalism.NG.BlockDetAlt.coeff_det_eq (R' : Subalgebra O (X' → Matrix d d (FractionRing O)))
    (a : Matrix d d (PowerSeries (X' → FractionRing O))) (ha : a ∈ goodM R') (n : ℕ) (x' : X') :
    PowerSeries.coeff n a.det x' = PowerSeries.coeff (n + Fintype.card d) (psi (n + Fintype.card d)
      (Matrix.det (∑ j : Fin (n + Fintype.card d),
        (MvPolynomial.X j : MvPolynomial _ (FractionRing O)) •
          (((⟨coefMat j.1 a, ha j.1⟩ : R') : X' → Matrix d d (FractionRing O)) x').map
            MvPolynomial.C))) := by sorry
