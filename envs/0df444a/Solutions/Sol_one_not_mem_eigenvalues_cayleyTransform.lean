-- Prove2me | solution 1 for one_not_mem_eigenvalues_cayleyTransform
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:53:21.609454+00:00
-- url     : https://prove2.me/submissions/1317e97d-ded0-48d0-86ed-25af6307f3a8

import Definitions.Def_Spectral_Cayley_Basic
import Definitions.Def_Spectral_Cayley_Unitary
import Theorems.Thm_add_I_surjective_of_isSelfAdjoint
import Theorems.Thm_cayleyTransform_apply_plus


set_option autoImplicit false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) :
    ∀ x, cayleyTransform A hA x = x → x = 0 := by
  intro y hy
  obtain ⟨x, hx⟩ := add_I_surjective_of_isSelfAdjoint A hA y
  change A x + Complex.I • (x : E) = y at hx
  have heq : A x - Complex.I • (x : E) = A x + Complex.I • (x : E) := by
    calc
      A x - Complex.I • (x : E) = cayleyTransform A hA
          (A x + Complex.I • (x : E)) := (cayleyTransform_apply_plus A hA x).symm
      _ = cayleyTransform A hA y := by rw [hx]
      _ = y := hy
      _ = A x + Complex.I • (x : E) := hx.symm
  rw [sub_eq_add_neg] at heq
  have hneg : -(Complex.I • (x : E)) = Complex.I • (x : E) :=
    add_left_cancel heq
  have htwo : (2 : ℂ) • (Complex.I • (x : E)) = 0 := by
    rw [two_smul]
    calc
      Complex.I • (x : E) + Complex.I • (x : E) =
          -(Complex.I • (x : E)) + Complex.I • (x : E) :=
        congrArg (fun z : E => z + Complex.I • (x : E)) hneg.symm
      _ = 0 := neg_add_cancel _
  have hIx : Complex.I • (x : E) = 0 :=
    (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  have hxE : (x : E) = 0 :=
    (smul_eq_zero.mp hIx).resolve_left Complex.I_ne_zero
  have hx0 : x = 0 := Subtype.ext hxE
  rw [← hx, hx0]
  change A (0 : A.domain) + Complex.I • ((0 : A.domain) : E) = 0
  rw [LinearPMap.map_zero A, Submodule.coe_zero, smul_zero, add_zero]
