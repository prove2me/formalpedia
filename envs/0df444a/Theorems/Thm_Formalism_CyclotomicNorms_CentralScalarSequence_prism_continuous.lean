-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_CentralScalarSequence_prism_continuous
-- name    : Formalism.CyclotomicNorms.CentralScalarSequence.prism_continuous
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:53:53.666846+00:00
-- url     : https://prove2.me/theorems/340038a8-921e-4012-ad38-e51f932f020d
-- title:
--   Central Scalar Sequence: prism continuous
-- statement:
--   The Central Scalar Sequence construction uses the prism continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/Central.lean#L177-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/Central.lean#L177-L183

import Definitions.Def_Formalism_CyclotomicNorms_StatementA
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_Central
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.CyclotomicNorms
open Formalism.CyclotomicNorms.CentralScalarSequence
variable {G : Type} [Group G]
variable {R W : Type} [CommRing R] [AddCommGroup W] [Module R W]

theorem Formalism.CyclotomicNorms.CentralScalarSequence.prism_continuous [TopologicalSpace G] [TopologicalSpace W] [DiscreteTopology W] {n : ℕ}
    (z : G) (f : (Fin (n + 1) → G) → W) (hf : Continuous f) : Continuous (prism R z f) := by sorry
