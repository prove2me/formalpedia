-- Prove2me | solution 1 for crouzeix_palencia_of_antitone_compact_auxiliary_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:38:04.076494+00:00
-- url     : https://prove2.me/submissions/a183877c-2f56-4680-ae59-2a66400b321b

import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Definitions.Def_Operator_Crouzeix_CompactThickeningApprox
import Definitions.Def_Operator_Crouzeix_PalenciaApproximation
import Definitions.Def_Operator_Crouzeix_PalenciaExhaustion
import Theorems.Thm_crouzeix_palencia_of_tendsto_auxiliary_bounds
import Theorems.Thm_tendsto_polynomialSupNorm_atTop_of_antitone_isCompact


set_option autoImplicit false
open Filter Set
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (K : ℕ → Set ℂ)
    (hanti : Antitone K) (hcompact : ∀ n, IsCompact (K n))
    (hnonempty : ∀ n, (K n).Nonempty)
    (hinter : (⋂ n, K n) = closure (numericalRange A))
    (haux : ∀ (p : Polynomial ℂ) (n : ℕ), ∃ G : E →L[ℂ] E,
      ‖Polynomial.aeval A p + star G‖ ≤ 2 * polynomialSupNorm p (K n) ∧
      ‖Polynomial.aeval A p * G‖ ≤ polynomialSupNorm p (K n) ^ 2) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  apply crouzeix_palencia_of_tendsto_auxiliary_bounds A
  intro p
  refine ⟨fun n ↦ polynomialSupNorm p (K n), ?_, haux p⟩
  have hlim := tendsto_polynomialSupNorm_atTop_of_antitone_isCompact
    p K hanti hcompact hnonempty
  rw [hinter] at hlim
  exact hlim
