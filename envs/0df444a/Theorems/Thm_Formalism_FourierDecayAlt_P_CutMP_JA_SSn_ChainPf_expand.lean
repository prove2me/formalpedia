-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_JA_SSn_ChainPf_expand
-- name    : Formalism.FourierDecayAlt.P.CutMP.JA.SSn.ChainPf.expand
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T06:20:28.596884+00:00
-- url     : https://prove2.me/theorems/47794b17-d023-580f-b721-00a57f710cfd
-- title:
--   Chain Pf: expand
-- statement:
--   The Chain Pf construction uses the expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJABddSSnChainPf.lean#L75-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJABddSSnChainPf.lean#L75-L145

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJABddSSnChain
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJABddSSnChainPf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA Formalism.FourierDecayAlt.P.CutMP.JA.SSn Formalism.FourierDecayAlt.P.CutMP.JA.SSn.ChainPf
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {V E' : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup E'] [NormedSpace ℂ E']

theorem Formalism.FourierDecayAlt.P.CutMP.JA.SSn.ChainPf.expand {Ψ : V → E'} (hΨ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ) {F : Mat k r → V}
    {U : Set (Mat k r)} (hU : IsOpen U) (hF : CkOn ⊤ (U ∩ GV k r) F) :
    ∀ w : List (Bool × Mat k r), (∀ y ∈ w, inLie k r y.2) →
      ∃ ts : List (Tm k r), ts.length ≤ (w.length + 1).factorial ∧
        (∀ t ∈ ts, t.j ≤ w.length ∧ (∑ i, (t.ws i).length) = w.length ∧ ∀ i, (t.ws i).Sublist w) ∧
        ∀ g ∈ U, g ∈ GV k r → Dw w (fun g => Ψ (F g)) g = (ts.map fun t => tval Ψ F t g).sum := by sorry
