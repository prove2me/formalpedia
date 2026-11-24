-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_landau_local3
-- name    : Formalism.ZeroFreeDirichlet.landau_local3
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:46:59.997455+00:00
-- url     : https://prove2.me/theorems/60224d53-f69d-40c5-988e-7018914a630a
-- title:
--   Zero Free Dirichlet: landau local3
-- statement:
--   The Zero Free Dirichlet construction uses the landau local3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/LandauLocal3.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/LandauLocal3.lean#L8-L9

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_ExistsLocalZeroExpansionOfBound
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LandauLocal3
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet

theorem Formalism.ZeroFreeDirichlet.landau_local3 : LandauLocal3 := by sorry
