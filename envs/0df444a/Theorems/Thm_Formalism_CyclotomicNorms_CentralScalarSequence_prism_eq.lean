-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_CentralScalarSequence_prism_eq
-- name    : Formalism.CyclotomicNorms.CentralScalarSequence.prism_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:53:43.226813+00:00
-- url     : https://prove2.me/theorems/e88826c8-7a03-4641-8704-d22eaf652288
-- title:
--   Central Scalar Sequence: prism eq
-- statement:
--   The Central Scalar Sequence construction uses the prism eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/Central.lean#L167-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/Central.lean#L167-L175

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

theorem Formalism.CyclotomicNorms.CentralScalarSequence.prism_eq {n : ℕ} (z : G) (f : (Fin (n + 1) → G) → W) (x : Fin n → G) (v : ℕ → G)
    (hx : ∀ k : Fin n, x k = v k) :
    prism R z f x = ∑ i ∈ range (n + 1), (-1 : R) ^ i • f (fun k => insN i z v k) := by sorry
