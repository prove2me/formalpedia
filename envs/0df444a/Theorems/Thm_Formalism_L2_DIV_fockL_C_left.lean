-- Prove2me | Theorems.Thm_Formalism_L2_DIV_fockL_C_left
-- name    : Formalism.L2.DIV.fockL_C_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:52:00.573034+00:00
-- url     : https://prove2.me/theorems/1cd5961f-c4e0-41e2-b16d-a206f36bd93d
-- title:
--   DIV: fock L C left
-- statement:
--   The DIV construction uses the fock L C left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/CoefModLemmas.lean#L366-L368
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/CoefModLemmas.lean#L366-L368

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
variable {K : Type} [Field K] [StarRing K]

theorem Formalism.L2.DIV.fockL_C_left {σ : Type} (a : K) (g : MvPolynomial σ K) : fockL (C a) g = star a * constantCoeff g := by sorry
