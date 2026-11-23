-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A6x8_Adic_root_near
-- name    : Formalism.FourierDecayAlt.P.A6x8.Adic.root_near
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:29:02.975984+00:00
-- url     : https://prove2.me/theorems/929fd696-016b-4647-ba4a-20cc09656417
-- title:
--   Adic: root near
-- statement:
--   The Adic construction uses the root near property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GramKernelHermitian.lean#L276-L293
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GramKernelHermitian.lean#L276-L293

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.A5 Formalism.DoubleCosetMeasures Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x8
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
variable {R : Subring K} {ϖ : Kˣ}

theorem Formalism.FourierDecayAlt.P.A6x8.Adic.root_near (h : Adic R ϖ) (hn : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) (s : ℕ) (hs : 1 ≤ s)
    {E : Set K} (hE : E ∈ 𝓝 (0 : K)) :
    ∃ a : Kˣ, (a : K) ∈ I R (ϖ : K) ∧ ∀ b : K, Near R (a : K) b → ∃ κ : K, κ ^ s = b ∧ κ - 1 ∈ E := by sorry
