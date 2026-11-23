-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_Sqf_monicOf_coeffs
-- name    : Formalism.CyclotomicNorms.Sqf.monicOf_coeffs
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:13:15.476447+00:00
-- url     : https://prove2.me/theorems/9027235a-d02e-4b24-998f-6d0071859605
-- title:
--   Sqf: monic Of coeffs
-- statement:
--   The Sqf construction uses the monic Of coeffs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/NonsquarefreeMonicBoundHolds.lean#L36-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/NonsquarefreeMonicBoundHolds.lean#L36-L46

import Definitions.Def_Formalism_CyclotomicNorms_StatementI
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_NonsquarefreeMonicBoundHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
noncomputable section
open Formalism Formalism.CyclotomicNorms
open Formalism.CyclotomicNorms.Sqf
variable {K : Type} [Field K]

theorem Formalism.CyclotomicNorms.Sqf.monicOf_coeffs (p : K[X]) (hp : p.Monic) {m : ℕ} (hd : p.natDegree = m) :
    monicOf (fun i : Fin m => p.coeff i) = p := by sorry
