-- Prove2me | Theorems.Thm_Formalism_L2_Pj_Crude_crExpSum
-- name    : Formalism.L2.Pj.Crude.crExpSum
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:39:06.514381+00:00
-- url     : https://prove2.me/theorems/4aca0d1f-6b20-4e88-b283-6abaa870a0e6
-- title:
--   Crude: cr Exp Sum
-- statement:
--   The Crude construction uses the cr Exp Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeMin.lean#L263-L284
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeMin.lean#L263-L284

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RowDeg
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeMin
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
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.Crude
open MvPolynomial Formalism.L2.Pj
variable {T : Type} [Fintype T] [DecidableEq T] (r : T → ℕ) (n : ℕ)
variable {r n}

theorem Formalism.L2.Pj.Crude.crExpSum (a : T → ℕ → ℕ) (ha : Dom r a) (σ : T) (i : Fin (r σ)) :
    (∑ kk : Fin (r σ), if (i : ℕ) < (kk : ℕ) + 1 then crExp r a σ kk else 0) = a σ i := by sorry
