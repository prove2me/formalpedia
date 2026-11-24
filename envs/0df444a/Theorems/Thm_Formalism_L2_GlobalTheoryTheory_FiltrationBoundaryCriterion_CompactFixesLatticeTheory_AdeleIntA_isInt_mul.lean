-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_FiltrationBoundaryCriterion_CompactFixesLatticeTheory_AdeleIntA_isInt_mul
-- name    : Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA.isInt_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:57:13.950772+00:00
-- url     : https://prove2.me/theorems/fd0193f9-3301-4d3e-8011-7de9dab11119
-- title:
--   Adele Int A: is Int mul
-- statement:
--   The Adele Int A construction uses the is Int mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL1/CompactFixesLattice/AdeleIntA.lean#L276-L279
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL1/CompactFixesLattice/AdeleIntA.lean#L276-L279

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL1_CompactFixesLattice_AdeleIntA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]

theorem Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA.isInt_mul {a b : FiniteAdeleRing R K} (ha : IsInt a) (hb : IsInt b) : IsInt (a * b) := by sorry
