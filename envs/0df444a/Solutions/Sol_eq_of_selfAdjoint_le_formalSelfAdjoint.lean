-- Prove2me | solution 1 for eq_of_selfAdjoint_le_formalSelfAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:01:59.098488+00:00
-- url     : https://prove2.me/submissions/004a40a5-6ed7-4d36-9d8c-63e05e7566da

import Definitions.Def_Spectral_Cayley_Basic
import Definitions.Def_Spectral_PVM_Unbounded
import Definitions.Def_Spectral_Spectral_CayleyCalculus

set_option autoImplicit false
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A B : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A)
    (hAB : A ≤ B) (hB : B.IsFormalAdjoint B) : B = A := by
  have hformal : A.IsFormalAdjoint B := by
    intro x y
    let xB : B.domain := ⟨x, hAB.1 x.property⟩
    calc
      @inner ℂ E _ (A x) (y : E) = @inner ℂ E _ (B xB) (y : E) := by
        rw [hAB.2 (x := x) (y := xB) rfl]
      _ = @inner ℂ E _ (x : E) (B y) := hB xB y
  have hBA : B ≤ A.adjoint := hformal.le_adjoint hA.dense_domain
  rw [LinearPMap.isSelfAdjoint_def.mp hA] at hBA
  exact le_antisymm hBA hAB
