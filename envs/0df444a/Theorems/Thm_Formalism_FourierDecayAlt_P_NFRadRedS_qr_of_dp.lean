-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NFRadRedS_qr_of_dp
-- name    : Formalism.FourierDecayAlt.P.NFRadRedS.qr_of_dp
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T02:06:52.457326+00:00
-- url     : https://prove2.me/theorems/66599c5e-05be-5ff9-bafe-defc6b4672dc
-- title:
--   NFRad Red S: qr of dp
-- statement:
--   The NFRad Red S construction uses the qr of dp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NFRadRedS.lean#L124-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NFRadRedS.lean#L124-L128

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

theorem Formalism.FourierDecayAlt.P.NFRadRedS.qr_of_dp {c : Fin r → ℂ} {g : Q.Mx k r} (hc : c ∈ OmX r) (hg : g ∈ Qx5.Dp k r z z') :
    (c, zetaL k r z z' (Fin.last r) g) ∈ QR k r z z' := by sorry
