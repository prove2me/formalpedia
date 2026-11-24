-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_nu_left
-- name    : Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1.nu_left
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T16:22:16.921107+00:00
-- url     : https://prove2.me/theorems/26943c79-2475-4985-af40-541eb8fe1d1f
-- title:
--   R1: nu left
-- statement:
--   The R1 construction uses the nu left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RankOneEmbeddings.lean#L553-L585
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RankOneEmbeddings.lean#L553-L585

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RankOneEmbeddings Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1.nu_left (CWb : ClosedWb) (CW : ClosedW) (UF : UWbFacts) (HI : HypInv) (z z' : Vc k r)
    {s : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hs : MeasSec s) (hsu : ∀ ζ, (s ζ)ᴴ * Hb k * s ζ = Hb k)
    (hk : 1 ≤ k) (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z')
    (hsec : IsSection k r z z' s)
    {μW μW' : Measure (Mt k r)} (hW : IsHaarOn (UWset k r z) μW) (hW' : IsHaarOn (UWset k r z') μW')
    (a : Mat k r) (ha : a ∈ UWb k r) : (nu z z' s μW μW').map (lmulM a) = nu z z' s μW μW' := by sorry
