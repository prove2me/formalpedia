-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Misc_tpolyProd_succ
-- name    : Formalism.FourierDecayAlt.P.Misc.tpolyProd_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:26:13.896571+00:00
-- url     : https://prove2.me/theorems/c2f79d50-b0e3-4174-8c4e-8002b6f761f0
-- title:
--   Misc: tpoly Prod succ
-- statement:
--   The Misc construction uses the tpoly Prod succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TransferProductMonic.lean#L27-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TransferProductMonic.lean#L27-L30

import Definitions.Def_Formalism_HermitianCurvature_StatementI
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferProductMonic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Misc
open Formalism.FourierDecayAlt.I Finset Polynomial

theorem Formalism.FourierDecayAlt.P.Misc.tpolyProd_succ {A : Type} [Ring A] (n : ℕ) (p c ci : ℕ → A) :
    TpolyProd (n + 1) p c ci = Tpoly (p (n + 1)) (c (n + 1)) (ci (n + 1)) * TpolyProd n p c ci := by sorry
