-- Prove2me | Theorems.Thm_Formalism_L2_NX_inParah_one
-- name    : Formalism.L2.NX.inParah_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:15:26.507865+00:00
-- url     : https://prove2.me/theorems/bb62bf32-8a58-4427-9817-a92ed780df72
-- title:
--   NX: in Parah one
-- statement:
--   The NX construction uses the in Parah one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/ExpDefs.lean#L302-L310
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/ExpDefs.lean#L302-L310

import Mathlib
import Definitions.Def_Formalism_AlgebraicWeights_IsAlgWeight
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.L2 Formalism.L2.NX
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
local notation3 "L⁺" => NumberField.maximalRealSubfield L

theorem Formalism.L2.NX.inParah_one (v : HeightOneSpectrum (𝓞 L⁺)) (r : ℕ) :
    InParah v r (1 : Matrix (Fin n) (Fin n) (v.adicCompletion L⁺)) := by sorry
