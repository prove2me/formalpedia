-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_JA_SSn_ChainPf_tval_hasDerivAt
-- name    : Formalism.FourierDecayAlt.P.CutMP.JA.SSn.ChainPf.tval_hasDerivAt
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T06:20:56.168389+00:00
-- url     : https://prove2.me/theorems/81b5d35d-5cc7-4df4-8e2f-926f8e414f89
-- title:
--   Chain Pf: tval has Deriv At
-- statement:
--   The Chain Pf construction uses the tval has Deriv At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJABddSSnChainPf.lean#L39-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJABddSSnChainPf.lean#L39-L73

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

theorem Formalism.FourierDecayAlt.P.CutMP.JA.SSn.ChainPf.tval_hasDerivAt {Ψ : V → E'} (hΨ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ) {F : Mat k r → V}
    {U : Set (Mat k r)} (hF : CkOn ⊤ (U ∩ GV k r) F) {x : Bool × Mat k r} (hx : inLie k r x.2)
    (t : Tm k r) (hws : ∀ i, ∀ y ∈ t.ws i, inLie k r y.2) {g : Mat k r} (hgU : g ∈ U) (hg : g ∈ GV k r) :
    HasDerivAt (fun s : ℝ => tval Ψ F t (crv x g s)) (((tnext x t).map fun t' => tval Ψ F t' g).sum) 0 := by sorry
