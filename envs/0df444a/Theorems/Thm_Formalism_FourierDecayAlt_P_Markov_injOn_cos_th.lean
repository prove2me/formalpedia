-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Markov_injOn_cos_th
-- name    : Formalism.FourierDecayAlt.P.Markov.injOn_cos_th
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:54:09.088491+00:00
-- url     : https://prove2.me/theorems/bc996989-f9e3-43a7-b159-85e4727f3ed7
-- title:
--   Markov: inj On cos th
-- statement:
--   The Markov construction uses the inj On cos th property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Markov.lean#L55-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Markov.lean#L55-L56

import Definitions.Def_Formalism_HermitianCurvature_StatementE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Markov
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Markov
open Polynomial Real Finset

theorem Formalism.FourierDecayAlt.P.Markov.injOn_cos_th (n : ℕ) : Set.InjOn (fun k => cos (th n k)) (Finset.range n : Finset ℕ) := by sorry
