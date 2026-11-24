-- Prove2me | Theorems.Thm_Formalism_HF_hostDensityArith_of
-- name    : Formalism.HF.hostDensityArith_of
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:24:08.500798+00:00
-- url     : https://prove2.me/theorems/47ef8619-ccc2-4527-bb38-f26ec641c367
-- title:
--   HF: host Density Arith of
-- statement:
--   The HF construction uses the host Density Arith of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DirichletDensity/DirichletDensityProofs/HostDensityArith.lean#L213-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DirichletDensity/DirichletDensityProofs/HostDensityArith.lean#L213-L217

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
open Formalism Formalism.HF

theorem Formalism.HF.hostDensityArith_of (hAP : Formalism.HF.APLogDensity) (hLD : Formalism.HF.LogToDir) :
    Formalism.HF.HostDensityArith := by sorry
