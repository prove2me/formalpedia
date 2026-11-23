-- Prove2me | Theorems.Thm_Formalism_NormUnitaryCountingLemmas_NU_ip_self
-- name    : Formalism.NormUnitaryCountingLemmas.NU.ip_self
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:19:30.248854+00:00
-- url     : https://prove2.me/theorems/b20810cb-bb32-4f9e-a1c7-43419e700ad0
-- title:
--   NU: ip self
-- statement:
--   The NU construction uses the ip self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/NormUnitary.lean#L115-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/NormUnitary.lean#L115-L120

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_NormUnitary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
open Formalism Formalism.NormUnitaryCountingLemmas Formalism.NormUnitaryCountingLemmas.NU
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem Formalism.NormUnitaryCountingLemmas.NU.ip_self (F : MvPolynomial σ ℂ) : ip F F = (FR F : ℂ) := by sorry
