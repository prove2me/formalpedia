-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_relT
-- name    : Formalism.FourierDecayAlt.P.Wd6.relT
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:33:51.200635+00:00
-- url     : https://prove2.me/theorems/e1761471-e40d-41f8-be7c-3ff9f3a5f0f4
-- title:
--   Wd6: rel T
-- statement:
--   The Wd6 construction uses the rel T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EntryCommuteTransposedRMatrix.lean#L249-L260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EntryCommuteTransposedRMatrix.lean#L249-L260

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd6
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [Ring A] [Algebra K A] [Fintype S] [DecidableEq S]

theorem Formalism.FourierDecayAlt.P.Wd6.relT (p c ci : A) (D Y Y' : K) (h1 : D • (p * c) - D • (c * p) = (Y - Y') • c)
    (h2 : D • (p * ci) - D • (ci * p) = (Y' - Y) • ci) (h3 : c * ci = ci * c) :
    Rel (Tm Y p c ci) (Tm Y' p c ci) D := by sorry
