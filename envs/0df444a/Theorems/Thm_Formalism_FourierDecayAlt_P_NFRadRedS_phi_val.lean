-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NFRadRedS_phi_val
-- name    : Formalism.FourierDecayAlt.P.NFRadRedS.phi_val
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T02:14:08.450818+00:00
-- url     : https://prove2.me/theorems/4f30e598-56d0-5822-90cc-3a6a72962b9f
-- title:
--   NFRad Red S: phi val
-- statement:
--   The NFRad Red S construction uses the phi val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NFRadRedS.lean#L130-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NFRadRedS.lean#L130-L141

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NFRadRedA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NFRadRedS
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_comp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_HatData_Good_comp

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

theorem Formalism.FourierDecayAlt.P.NFRadRedS.phi_val (hπ : IsCRepOn (UWset k r z) π) (hπ' : IsCRepOn (UWset k r z') π')
    {φ : (Fin r → ℂ) × ℂ → (Wq →L[ℂ] Wp)} (hφ : ∀ q ∈ QR k r z z', φ q ∈ Fib k r z z' μsec π π' q.2)
    {c : Fin r → ℂ} {g : Q.Mx k r} (hx : (c, g) ∈ DomR k r z z') {a b : Q.Mx k r} (ha : a ∈ UWset k r z)
    (hb : b ∈ UWset k r z') (hg : g = a * muZ k r μsec (zetaL k r z z' (Fin.last r) g) * b) :
    Phi k r z z' μsec π π' φ c g = (π a).comp ((φ (c, zetaL k r z z' (Fin.last r) g)).comp (π' b)) := by sorry
