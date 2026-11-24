-- Prove2me | Theorems.Thm_Formalism_L2_DIV_colLat_one_eq
-- name    : Formalism.L2.DIV.colLat_one_eq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:55:25.338399+00:00
-- url     : https://prove2.me/theorems/841975b6-017d-4853-927b-158da9d75393
-- title:
--   DIV: col Lat one eq
-- statement:
--   The DIV construction uses the col Lat one eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/CoefModLemmas.lean#L741-L754
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/CoefModLemmas.lean#L741-L754

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefModLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K]

theorem Formalism.L2.DIV.colLat_one_eq (B : GL (Fin 1) K) :
    colLat B = Submodule.span (𝓞 K) {fun _ : Fin 1 => (B : Matrix (Fin 1) (Fin 1) K) 0 0} := by sorry
