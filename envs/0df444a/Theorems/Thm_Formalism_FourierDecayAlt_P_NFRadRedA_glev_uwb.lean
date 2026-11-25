-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NFRadRedA_glev_uwb
-- name    : Formalism.FourierDecayAlt.P.NFRadRedA.glev_uwb
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T01:54:34.344164+00:00
-- url     : https://prove2.me/theorems/bbc59341-ef1a-5727-8bc5-333ab1801b07
-- title:
--   NFRad Red A: glev uwb
-- statement:
--   The NFRad Red A construction uses the glev uwb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NFRadRedA.lean#L25-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NFRadRedA.lean#L25-L25

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellInversePair
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellOpenDomain
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellZetaMinors
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NFRadRedA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NFRadRedA
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.NF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Classical
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}

theorem Formalism.FourierDecayAlt.P.NFRadRedA.glev_uwb {g : Q.Mx k r} (hg : g ∈ Glev k r (Fin.last r)) : g ∈ B2.UWb k r := by sorry
