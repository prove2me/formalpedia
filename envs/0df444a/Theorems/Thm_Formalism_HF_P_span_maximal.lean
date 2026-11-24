-- Prove2me | Theorems.Thm_Formalism_HF_P_span_maximal
-- name    : Formalism.HF.P.span_maximal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:23:49.669821+00:00
-- url     : https://prove2.me/theorems/e9b154f5-3e8f-45df-806f-37859b742606
-- title:
--   P: span maximal
-- statement:
--   The P construction uses the span maximal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DirichletDensity/DirichletDensityProofs/HostDensity.lean#L21-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DirichletDensity/DirichletDensityProofs/HostDensity.lean#L21-L27

import Mathlib
import Definitions.Def_Formalism_DirichletDensity_Statement
import Definitions.Def_Formalism_CMTypeGalois_HalfTypesFromGeneral
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_HostDensity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal Filter Topology Formalism.Q3
noncomputable section
open Formalism Formalism.HF Formalism.HF.P

theorem Formalism.HF.P.span_maximal (p : ℕ) (hp : p.Prime) : (span {(p : ℤ)} : Ideal ℤ).IsMaximal := by sorry
