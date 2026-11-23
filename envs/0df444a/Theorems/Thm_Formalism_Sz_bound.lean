-- Prove2me | Theorems.Thm_Formalism_Sz_bound
-- name    : Formalism.Sz_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:13:06.102852+00:00
-- url     : https://prove2.me/theorems/54fbc0ff-313c-4da3-a0f5-5a556c56f482
-- title:
--   Formalism: Sz bound
-- statement:
--   The Formalism construction uses the Sz bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/ZetaLandau.lean#L208-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/ZetaLandau.lean#L208-L235

import Definitions.Def_Formalism_StatementU
import Definitions.Def_Formalism_ZetaNonvanishing_OfRealNeOfRealOfLt
import Definitions.Def_Formalism_ZetaNonvanishing_LandauEq
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSgen
import Definitions.Def_Formalism_ZetaNonvanishing_MellinElem
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaRealNonvanish
import Definitions.Def_Formalism_ZetaNonvanishing_LogDerivZeroFree
import Definitions.Def_Formalism_ZetaNonvanishing_MellinDeriv
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaLandau
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Formalism
open ArithmeticFunction

theorem Formalism.Sz_bound {x X : ℝ} (hx1 : 1 ≤ x) (hxX : x ≤ X) :
    0 ≤ Sz x ∧ Sz x ≤ X * ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, Λ n := by sorry
