-- Prove2me | Theorems.Thm_DensInertW_cg_gram
-- name    : DensInertW.cg_gram
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:39:11.954899+00:00
-- url     : https://prove2.me/theorems/6db337ec-26bc-4fc8-8f9e-8ad0c0147d57
-- title:
--   Dens Inert W: cg gram
-- statement:
--   The Dens Inert W construction uses the cg gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/RepCountCongruenceInvariant.lean#L94-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/RepCountCongruenceInvariant.lean#L94-L104

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_AnisoPeelAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_ExistsTraceNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_RepCountCongruenceInvariant
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
open DensInertW

theorem DensInertW.cg_gram (K L : Type) [Field K] [Fintype K] [Field L] [Algebra K L] {m n : ℕ}
    (M : Matrix (Fin n) (Fin n) L) (Q G : Matrix (Fin m) (Fin m) L) (X : Fin m → Fin n → L)
    (hX : ∀ k l, hf (Fintype.card K) M (X k) (X l) = G k l) (i j : Fin m) :
    hf (Fintype.card K) M (cgComb Q X i) (cgComb Q X j) =
      (Q * G * (Q.map (fun y => y ^ Fintype.card K)).transpose) i j := by sorry
