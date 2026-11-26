-- Prove2me | solution 1 for section5_basis_permutation_conjugation
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:41:54.988998+00:00
-- url     : https://prove2.me/submissions/29cd14a4-4e64-404b-baa6-3c8a1634f34d

import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QuantumLTF_Membership_Supplement_probMixed
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Mathlib
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership

/-! Every circuit over the published NOT/CNOT/Toffoli gate set acts as an exact
permutation of basis strings, including inputs with arbitrary workspace bits. -/









theorem section5_basis_permutation_matrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) (f : Equiv.Perm ι)
    (hact : ∀ x, act U (ket x)=ket (f x)) (y x : ι) :
    U y x=if y=f x then 1 else 0 := by
  have hh := congrArg (fun v : EuclideanSpace ℂ ι => v y) (hact x)
  change Matrix.mulVec U (Pi.single x (1:ℂ)) y=(Pi.single (f x) (1:ℂ) : ι → ℂ) y at hh
  simpa [Matrix.mulVec_single,Pi.single_apply,eq_comm] using hh

end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U ρ : Matrix ι ι ℂ) (f : Equiv.Perm ι)
    (hact : ∀ x, act U (ket x)=ket (f x)) (x y : ι) :
    (U*ρ*U.conjTranspose) (f x) (f y)=ρ x y := by
  have he := section5_basis_permutation_matrix U f hact
  have hleft (a j : ι) : (U*ρ) (f a) j=ρ a j := by
    simp [Matrix.mul_apply,he,f.injective.eq_iff]
  simp [Matrix.mul_apply,hleft,Matrix.conjTranspose_apply,he,f.injective.eq_iff]
