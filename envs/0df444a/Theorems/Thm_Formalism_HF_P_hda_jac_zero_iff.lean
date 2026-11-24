-- Prove2me | Theorems.Thm_Formalism_HF_P_hda_jac_zero_iff
-- name    : Formalism.HF.P.hda_jac_zero_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:24:34.974944+00:00
-- url     : https://prove2.me/theorems/31b21c15-f69c-485b-a3b7-73c51c9d1f53
-- title:
--   P: hda jac zero iff
-- statement:
--   The P construction uses the hda jac zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DirichletDensity/DirichletDensityProofs/HostDensityArith.lean#L10-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DirichletDensity/DirichletDensityProofs/HostDensityArith.lean#L10-L13

import Mathlib
import Definitions.Def_Formalism_DirichletDensity_Statement
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_HostDensityArith
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Finset Formalism.Q3
noncomputable section
open Formalism Formalism.HF Formalism.HF.P

theorem Formalism.HF.P.hda_jac_zero_iff (p : ℕ) [Fact p.Prime] (m : ℕ) :
    jacobiSym (m : ℤ) p = 0 ↔ p ∣ m := by sorry
