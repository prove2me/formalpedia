-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_zeta_minus_pole_eq
-- name    : Formalism.ZeroFreeDirichlet.zeta_minus_pole_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:44:21.289799+00:00
-- url     : https://prove2.me/theorems/0aaf5d1c-92de-4e84-a798-1e3a4b5c646b
-- title:
--   Zero Free Dirichlet: zeta minus pole eq
-- statement:
--   The Zero Free Dirichlet construction uses the zeta minus pole eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/BqEntire.lean#L27-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/BqEntire.lean#L27-L29

import Definitions.Def_Formalism_LandauZeroFreeBounds_SameCharacterLFunctionOne
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_BqEntire
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet

theorem Formalism.ZeroFreeDirichlet.zeta_minus_pole_eq {s : ℂ} (hs : s ≠ 1) : zetaSubPole s = riemannZeta s - 1 / (s - 1) := by sorry
