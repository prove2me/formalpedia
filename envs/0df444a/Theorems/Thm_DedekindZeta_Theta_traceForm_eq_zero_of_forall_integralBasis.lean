-- Prove2me | Theorems.Thm_DedekindZeta_Theta_traceForm_eq_zero_of_forall_integralBasis
-- name    : DedekindZeta.Theta.traceForm_eq_zero_of_forall_integralBasis
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:13:42.125336+00:00
-- url     : https://prove2.me/theorems/fb2766bb-faaa-4c9c-9ce7-f1bc871edf40
-- title:
--   Theta: trace Form eq zero of forall integral Basis
-- statement:
--   **Nondegeneracy of the real trace form** (the analytic input to the
--   fullness/ℚ-rationality argument). A point `ζ : K_ℝ` whose
--   trace-form pairing vanishes against every integral-basis element is `0`. Proof:
--   the pairings against `mixedEmbedding (integralBasis K i)` are the values of the
--   `ℝ`-linear functional `traceFormLin K ζ` on the `ℝ`-basis `latticeBasis K`, so
--   the functional vanishes identically; evaluating at the "conjugate" witness
--   `(ζ.1, conj ζ.2)` gives `∑ (ζ.1 w)² + 2 ∑ ‖ζ.2 w‖² = 0`, forcing `ζ = 0`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L659-L694
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L659-L694

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section

theorem DedekindZeta.Theta.traceForm_eq_zero_of_forall_integralBasis (ζ : mixedSpace K)
    (hz : ∀ i, traceForm K ζ (integralBasis K i) = 0) : ζ = 0 := by sorry
