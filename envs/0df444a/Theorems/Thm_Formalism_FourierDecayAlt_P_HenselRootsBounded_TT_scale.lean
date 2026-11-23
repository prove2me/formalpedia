-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_TT_scale
-- name    : Formalism.FourierDecayAlt.P.HenselRootsBounded.TT_scale
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:09:11.461627+00:00
-- url     : https://prove2.me/theorems/17f1a2bb-f56c-446b-b561-e072e850ff27
-- title:
--   Hensel Roots Bounded: TT scale
-- statement:
--   The Hensel Roots Bounded construction uses the TT scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HenselRootsBounded.lean#L490-L506
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HenselRootsBounded.lean#L490-L506

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HenselRootsBounded
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HenselRootsBounded
variable {K : Type} [CommRing K]

theorem Formalism.FourierDecayAlt.P.HenselRootsBounded.TT_scale {s : ℕ} {Cut : Set K} {τ : Kˣ} {F G : Kˣ → ℂ} (υ : Kˣ)
    (hcut : ∀ c : Kˣ, (c : K) ∈ Cut ↔ ((υ ^ s * c : Kˣ) : K) ∈ Cut)
    (hG : ∀ c z : Kˣ, (c : K) ∈ Cut → z ^ s = τ * c → F (z * υ) = G z) (c : Kˣ) :
    TT s Cut τ F (υ ^ s * c) = TT s Cut τ G c := by sorry
