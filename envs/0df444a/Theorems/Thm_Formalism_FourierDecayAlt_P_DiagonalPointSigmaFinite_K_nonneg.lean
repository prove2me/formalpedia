-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_K_nonneg
-- name    : Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.K_nonneg
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T21:14:20.422499+00:00
-- url     : https://prove2.me/theorems/440ed343-5dc0-4e21-9038-fac668091c67
-- title:
--   Diagonal Point Sigma Finite: K nonneg
-- statement:
--   The Diagonal Point Sigma Finite construction uses the K nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseEstimates.lean#L46-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseEstimates.lean#L46-L54

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseEstimates
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite
open Formalism.FourierDecayAlt.G Matrix MeasureTheory Filter Topology
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.K_nonneg {m k : ℕ} {Kc : Set ℂ} {A K : ℝ} {Φ : Mat (m + 1 + 1) → V} {D : ℂ} (hD : D ∈ Kc)
    (h : DerivBound k (detSet (m + 1) Kc) (fun Z => K * min 1 (‖Z‖ ^ (-A))) Φ) : 0 ≤ K := by sorry
