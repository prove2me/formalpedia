-- Prove2me | Theorems.Thm_Formalism_ELL_SubstitutionCoefficientCongruence_degree_le_of_mem_antidiagonal
-- name    : Formalism.ELL.SubstitutionCoefficientCongruence.degree_le_of_mem_antidiagonal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:19:00.947234+00:00
-- url     : https://prove2.me/theorems/0a573f17-4fb4-4844-be98-9053422bb0ba
-- title:
--   Substitution Coefficient Congruence: degree le of mem antidiagonal
-- statement:
--   The Substitution Coefficient Congruence construction uses the degree le of mem antidiagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/NDeriv.lean#L65-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/NDeriv.lean#L65-L69

import Definitions.Def_Formalism_EllipticTorsion_Statement
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_NDeriv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
open Formalism Formalism.ELL Formalism.ELL.SubstitutionCoefficientCongruence
variable {R : Type*} [CommRing R] {σ : Type*}

theorem Formalism.ELL.SubstitutionCoefficientCongruence.degree_le_of_mem_antidiagonal [DecidableEq σ] {d : σ →₀ ℕ} {x : (σ →₀ ℕ) × (σ →₀ ℕ)}
    (hx : x ∈ Finset.HasAntidiagonal.antidiagonal d) : x.1.degree ≤ d.degree := by sorry
