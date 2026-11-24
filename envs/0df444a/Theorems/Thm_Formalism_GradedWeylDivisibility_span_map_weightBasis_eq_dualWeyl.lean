-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_span_map_weightBasis_eq_dualWeyl
-- name    : Formalism.GradedWeylDivisibility.span_map_weightBasis_eq_dualWeyl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:54:20.334496+00:00
-- url     : https://prove2.me/theorems/64b3d62d-9901-4f01-b9db-2b41e668c9cb
-- title:
--   Graded Weyl Divisibility: span map weight Basis eq dual Weyl
-- statement:
--   The Graded Weyl Divisibility construction uses the span map weight Basis eq dual Weyl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/NablaLKBasis.lean#L9-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/NablaLKBasis.lean#L9-L26

import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_NablaLKBasis
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility

theorem Formalism.GradedWeylDivisibility.span_map_weightBasis_eq_dualWeyl {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] {k n : ℕ}
    {ν : Fin n → ℕ} {ι : Type} {b : ι → MvPolynomial (Fin k × Fin n) R} {μ : ι → (Fin k → ℕ)}
    (hb : IsWeightBasis R k n ν b μ) :
    Submodule.span K (Set.range fun i => map (algebraMap R K) (b i)) = dualWeyl K k n ν := by sorry
