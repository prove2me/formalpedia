-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NFRadRedS_wd
-- name    : Formalism.FourierDecayAlt.P.NFRadRedS.wd
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T02:08:49.710692+00:00
-- url     : https://prove2.me/theorems/30e9ac9b-a944-5d98-975e-75b4d34bdbb7
-- title:
--   NFRad Red S: wd
-- statement:
--   The NFRad Red S construction uses the wd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NFRadRedS.lean#L92-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NFRadRedS.lean#L92-L114

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

theorem Formalism.FourierDecayAlt.P.NFRadRedS.wd (hπ : IsCRepOn (UWset k r z) π) (hπ' : IsCRepOn (UWset k r z') π') {ζ : ℂ}
    {X : Wq →L[ℂ] Wp} (hX : X ∈ Fib k r z z' μsec π π' ζ)
    {a₁ a₂ b₁ b₂ : Q.Mx k r} (ha₁ : a₁ ∈ UWset k r z) (ha₂ : a₂ ∈ UWset k r z) (hb₁ : b₁ ∈ UWset k r z')
    (hb₂ : b₂ ∈ UWset k r z') (he : a₁ * muZ k r μsec ζ * b₁ = a₂ * muZ k r μsec ζ * b₂) :
    (π a₁).comp (X.comp (π' b₁)) = (π a₂).comp (X.comp (π' b₂)) := by sorry
