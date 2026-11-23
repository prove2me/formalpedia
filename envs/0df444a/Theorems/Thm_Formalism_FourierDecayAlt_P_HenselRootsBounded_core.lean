-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_core
-- name    : Formalism.FourierDecayAlt.P.HenselRootsBounded.core
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:09:23.853602+00:00
-- url     : https://prove2.me/theorems/349c8e4b-ed7a-41b5-b432-3ab323c016ca
-- title:
--   Hensel Roots Bounded: core
-- statement:
--   The Hensel Roots Bounded construction uses the core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HenselRootsBounded.lean#L508-L561
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HenselRootsBounded.lean#L508-L561

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

theorem Formalism.FourierDecayAlt.P.HenselRootsBounded.core {R : Subring K} {s : ℕ} {Cut : Set K} {τ : Kˣ} {F : Kˣ → ℂ}
    {cr : K ⧸ R.toAddSubgroup → Kˣ} (hcr : IsCr R cr)
    (hA : ∀ c c' : Kˣ, (c' : K) - c ∈ R → TT s Cut τ F c' = TT s Cut τ F c)
    (EE : Finset K) (hcard : EE.card ≠ 0) (G : K → Kˣ → ℂ)
    (hB : ∀ ε ∈ EE, ∃ lam : Kˣ, (lam : K) ∈ R ∧ ((lam⁻¹ : Kˣ) : K) ∈ R ∧
      ∀ c, TT s Cut τ F (lam * c) = TT s Cut τ (G ε) c)
    (hC : ∀ c : Kˣ, (c : K) ∈ Cut → ∀ z : Kˣ, z ^ s = τ * c → ∑ ε ∈ EE, G ε z = 0)
    (hfin1 : {x | (cr x : K) ∈ Cut}.Finite) (hfin2 : ∀ D : Kˣ, {z : Kˣ | z ^ s = D}.Finite) :
    ∑ᶠ x, TT s Cut τ F (cr x) = 0 := by sorry
