-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NFRadRedS_radRedSurj_of
-- name    : Formalism.FourierDecayAlt.P.NFRadRedS.radRedSurj_of
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T02:31:42.692921+00:00
-- url     : https://prove2.me/theorems/bb5883b0-7166-430c-8bfd-ed3b239fb4be
-- title:
--   NFRad Red S: rad Red Surj of
-- statement:
--   The NFRad Red S construction uses the rad Red Surj of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NFRadRedS.lean#L163-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NFRadRedS.lean#L163-L255

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NFRadRedA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NFRadRedS
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NFRadRedS
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.NF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Classical
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
  {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  {π : Q.Mx k r → (Wp →L[ℂ] Wp)} {π' : Q.Mx k r → (Wq →L[ℂ] Wq)}

theorem Formalism.FourierDecayAlt.P.NFRadRedS.radRedSurj_of (hL : LocSec) (hR : RepSmooth) : NF.RadRedSurj := by sorry
