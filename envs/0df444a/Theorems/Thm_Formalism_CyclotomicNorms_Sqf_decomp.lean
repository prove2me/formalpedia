-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_Sqf_decomp
-- name    : Formalism.CyclotomicNorms.Sqf.decomp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:11:15.471583+00:00
-- url     : https://prove2.me/theorems/d98eba37-50b7-4ba8-a9af-f09d40261491
-- title:
--   Sqf: decomp
-- statement:
--   The Sqf construction uses the decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/NonsquarefreeMonicBoundHolds.lean#L48-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/NonsquarefreeMonicBoundHolds.lean#L48-L73

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

theorem Formalism.CyclotomicNorms.Sqf.decomp (f : K[X]) (hf : f.Monic) (h0 : f.coeff 0 ≠ 0) (hsq : ¬ Squarefree f) :
    ∃ P h : K[X], P.Monic ∧ h.Monic ∧ 1 ≤ P.natDegree ∧ P.coeff 0 ≠ 0 ∧ f = P * P * h := by sorry
