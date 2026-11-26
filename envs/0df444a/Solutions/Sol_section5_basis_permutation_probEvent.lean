-- Prove2me | solution 1 for section5_basis_permutation_probEvent
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:41:56.364832+00:00
-- url     : https://prove2.me/submissions/08efda4d-7dbe-4f00-b4e3-8bb5ee2e5b37

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
section
set_option autoImplicit false

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement

/-! Exact measurement laws for reversible classical post-processing. These hold
for arbitrary input matrices, so coherences between measurement transcripts do
not have to be discarded by an unproved intermediate-measurement assumption. -/







theorem section5_basis_permutation_amplitude {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) (f : Equiv.Perm ι)
    (hact : ∀ x, act U (ket x)=ket (f x)) (ψ : EuclideanSpace ℂ ι) (x : ι) :
    act U ψ (f x)=ψ x := by
  have he := section5_basis_permutation_matrix U f hact
  change Matrix.mulVec U ψ.ofLp (f x)=ψ x
  simp [Matrix.mulVec,dotProduct,he,f.injective.eq_iff]



end
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) (f : Equiv.Perm ι)
    (hact : ∀ x, act U (ket x)=ket (f x)) (ψ : EuclideanSpace ℂ ι)
    (P : ι → Prop) [DecidablePred P] :
    probEvent (act U ψ) P=∑ x : ι, if P (f x) then prob ψ x else 0 := by
  have hp (x : ι) : prob (act U ψ) (f x)=prob ψ x := by
    simp only [prob,ket,EuclideanSpace.inner_single_left,map_one,one_mul]
    rw [section5_basis_permutation_amplitude U f hact]
  unfold probEvent
  rw [Finset.sum_filter,← Equiv.sum_comp f]
  simp only [hp]
