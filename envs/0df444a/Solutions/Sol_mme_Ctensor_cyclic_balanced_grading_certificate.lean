-- Prove2me | solution 1 for mme_Ctensor_cyclic_balanced_grading_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T03:49:37.8527+00:00
-- url     : https://prove2.me/submissions/9100d7d6-fe44-4853-b1dd-c5aa80ae97ed

import Definitions.Def_CTensorCyclicBalancedGradingCertificate
import Definitions.Def_mme_TypeGrading_permutation
import Definitions.Def_mme_TypeGrading_kron
import Definitions.Def_mme_cyclicSymmetrization_public_perm
import Theorems.Thm_mme_TypeGrading_kron_blockSubtensor_iso
import Theorems.Thm_mme_kronFin_respects_iso
import Theorems.Thm_mme_kronFin_MMObj_iso
import Theorems.Thm_mme_Ctensor_cyclic_dimension_products_common_volume

open MME TensorProduct PiTensorProduct BigOperators
open MME.TensorObj.TypeGrading

universe u

namespace MME

variable {K : Type u} [Field K]
variable {T : TensorObj K 3} {t : ℕ}

/-- Transport a grading backward across an equality of tensor objects. -/
noncomputable def gradingOfEq
    {A B : TensorObj K 3} (h : A = B)
    (G : B.TypeGrading t) : A.TypeGrading t :=
  h.symm ▸ G

theorem gradingOfEq_blockTensor_ne_zero_iff
    {A B : TensorObj K 3} (h : A = B)
    (G : B.TypeGrading t) (rho : Fin 3 → Fin t) :
    (gradingOfEq h G).blockTensor rho ≠ 0 ↔
      G.blockTensor rho ≠ 0 := by
  subst B
  rfl

theorem gradingOfEq_blockSubtensor_iso
    {A B : TensorObj K 3} (h : A = B)
    (G : B.TypeGrading t) (rho : Fin 3 → Fin t) :
    TensorObj.Isomorphic
      ((gradingOfEq h G).blockSubtensor rho)
      (G.blockSubtensor rho) := by
  subst B
  exact TensorObj.Isomorphic.refl _

theorem blockTensor_ne_zero_congr
    {A : TensorObj K 3} (G : A.TypeGrading t)
    {rho sigma : Fin 3 → Fin t} (h : rho = sigma) :
    G.blockTensor rho ≠ 0 ↔ G.blockTensor sigma ≠ 0 := by
  subst sigma
  rfl

/-- The product grading on the public presentation of a cyclic
symmetrization. -/
noncomputable def publicCyclicTripleGrading (G : T.TypeGrading t) :
    (TensorObj.kron T
      (TensorObj.kron
        (TensorObj.permObj cyclicPerm T)
        (TensorObj.permObj (cyclicPerm.trans cyclicPerm) T))).TypeGrading
      (t * (t * t)) :=
  kronGrading G
    (kronGrading
      (permObjGrading G cyclicPerm)
      (permObjGrading G (cyclicPerm.trans cyclicPerm)))

/-- The threefold product grading on the public presentation
`T ⊗ πT ⊗ π²T` of the cyclic symmetrization. -/
noncomputable def cyclicTripleGrading (G : T.TypeGrading t) :
    (cyclicSymmetrization T).TypeGrading (t * (t * t)) :=
  gradingOfEq (cyclicSymmetrization_eq_public_perm T)
    (publicCyclicTripleGrading G)

/-- Encode the three factor grades at one mode of a cyclic product. -/
def cyclicTripleGrade
    (rhoX rhoY rhoZ : Fin 3 → Fin t) (i : Fin 3) :
    Fin (t * (t * t)) :=
  finProdFinEquiv
    (rhoX i,
      finProdFinEquiv
        (rhoY (cyclicPerm.symm i),
          rhoZ ((cyclicPerm.trans cyclicPerm).symm i)))

/-- A nonzero cyclic product block forces the block of the unpermuted
factor to be nonzero. -/
theorem cyclicTripleGrading_blockTensor_ne_zero_first
    (G : T.TypeGrading t)
    (rhoX rhoY rhoZ : Fin 3 → Fin t)
    (h : (cyclicTripleGrading G).blockTensor
      (cyclicTripleGrade rhoX rhoY rhoZ) ≠ 0) :
    G.blockTensor rhoX ≠ 0 := by
  have hpub : (publicCyclicTripleGrading G).blockTensor
      (cyclicTripleGrade rhoX rhoY rhoZ) ≠ 0 :=
    (gradingOfEq_blockTensor_ne_zero_iff
      (cyclicSymmetrization_eq_public_perm T)
      (publicCyclicTripleGrading G)
      (cyclicTripleGrade rhoX rhoY rhoZ)).mp h
  exact kronGrading_blockTensor_ne_zero_left G
    (kronGrading
      (permObjGrading G cyclicPerm)
      (permObjGrading G (cyclicPerm.trans cyclicPerm)))
    rhoX
    (fun i ↦ finProdFinEquiv
      (rhoY (cyclicPerm.symm i),
        rhoZ ((cyclicPerm.trans cyclicPerm).symm i))) hpub

/-- A nonzero cyclic product block forces the block of the once-permuted
factor, expressed back in the original grading, to be nonzero. -/
theorem cyclicTripleGrading_blockTensor_ne_zero_second
    (G : T.TypeGrading t)
    (rhoX rhoY rhoZ : Fin 3 → Fin t)
    (h : (cyclicTripleGrading G).blockTensor
      (cyclicTripleGrade rhoX rhoY rhoZ) ≠ 0) :
    G.blockTensor rhoY ≠ 0 := by
  have hpub : (publicCyclicTripleGrading G).blockTensor
      (cyclicTripleGrade rhoX rhoY rhoZ) ≠ 0 :=
    (gradingOfEq_blockTensor_ne_zero_iff
      (cyclicSymmetrization_eq_public_perm T)
      (publicCyclicTripleGrading G)
      (cyclicTripleGrade rhoX rhoY rhoZ)).mp h
  have hinner := kronGrading_blockTensor_ne_zero_right G
    (kronGrading
      (permObjGrading G cyclicPerm)
      (permObjGrading G (cyclicPerm.trans cyclicPerm)))
    rhoX
    (fun i ↦ finProdFinEquiv
      (rhoY (cyclicPerm.symm i),
        rhoZ ((cyclicPerm.trans cyclicPerm).symm i))) hpub
  have hperm := kronGrading_blockTensor_ne_zero_left
    (permObjGrading G cyclicPerm)
    (permObjGrading G (cyclicPerm.trans cyclicPerm))
    (fun i ↦ rhoY (cyclicPerm.symm i))
    (fun i ↦ rhoZ ((cyclicPerm.trans cyclicPerm).symm i)) hinner
  intro hy
  apply hperm
  rw [permObjGrading_blockTensor G cyclicPerm rhoY, hy, map_zero]
  rfl

/-- A nonzero cyclic product block forces the block of the twice-permuted
factor, expressed back in the original grading, to be nonzero. -/
theorem cyclicTripleGrading_blockTensor_ne_zero_third
    (G : T.TypeGrading t)
    (rhoX rhoY rhoZ : Fin 3 → Fin t)
    (h : (cyclicTripleGrading G).blockTensor
      (cyclicTripleGrade rhoX rhoY rhoZ) ≠ 0) :
    G.blockTensor rhoZ ≠ 0 := by
  have hpub : (publicCyclicTripleGrading G).blockTensor
      (cyclicTripleGrade rhoX rhoY rhoZ) ≠ 0 :=
    (gradingOfEq_blockTensor_ne_zero_iff
      (cyclicSymmetrization_eq_public_perm T)
      (publicCyclicTripleGrading G)
      (cyclicTripleGrade rhoX rhoY rhoZ)).mp h
  have hinner := kronGrading_blockTensor_ne_zero_right G
    (kronGrading
      (permObjGrading G cyclicPerm)
      (permObjGrading G (cyclicPerm.trans cyclicPerm)))
    rhoX
    (fun i ↦ finProdFinEquiv
      (rhoY (cyclicPerm.symm i),
        rhoZ ((cyclicPerm.trans cyclicPerm).symm i))) hpub
  have hperm := kronGrading_blockTensor_ne_zero_right
    (permObjGrading G cyclicPerm)
    (permObjGrading G (cyclicPerm.trans cyclicPerm))
    (fun i ↦ rhoY (cyclicPerm.symm i))
    (fun i ↦ rhoZ ((cyclicPerm.trans cyclicPerm).symm i)) hinner
  intro hz
  apply hperm
  rw [permObjGrading_blockTensor G
    (cyclicPerm.trans cyclicPerm) rhoZ, hz, map_zero]
  rfl

/-- At one position, a block of the public cyclic product grading is the
nested Kronecker product of the corresponding three factor blocks. -/
theorem publicCyclicTripleGrading_blockSubtensor_iso
    (G : T.TypeGrading t)
    (rhoX rhoY rhoZ : Fin 3 → Fin t) :
    TensorObj.Isomorphic
      (TensorObj.kron (G.blockSubtensor rhoX)
        (TensorObj.kron
          ((permObjGrading G cyclicPerm).blockSubtensor
            (fun i ↦ rhoY (cyclicPerm.symm i)))
          ((permObjGrading G (cyclicPerm.trans cyclicPerm)).blockSubtensor
            (fun i ↦ rhoZ ((cyclicPerm.trans cyclicPerm).symm i)))))
      ((publicCyclicTripleGrading G).blockSubtensor
        (cyclicTripleGrade rhoX rhoY rhoZ)) := by
  let GY := permObjGrading G cyclicPerm
  let GZ := permObjGrading G (cyclicPerm.trans cyclicPerm)
  let sy : Fin 3 → Fin t := fun i ↦ rhoY (cyclicPerm.symm i)
  let sz : Fin 3 → Fin t := fun i ↦
    rhoZ ((cyclicPerm.trans cyclicPerm).symm i)
  have hinner := mme_TypeGrading_kron_blockSubtensor_iso GY GZ sy sz
  have hlift := TensorQ.mul_respects_iso
    (TensorObj.Isomorphic.refl (G.blockSubtensor rhoX)) hinner
  have houter := mme_TypeGrading_kron_blockSubtensor_iso
    G (kronGrading GY GZ) rhoX
      (fun i ↦ finProdFinEquiv (sy i, sz i))
  exact hlift.trans houter

/-- The same one-position block identification on the original
`cyclicSymmetrization` object. -/
theorem cyclicTripleGrading_blockSubtensor_iso
    (G : T.TypeGrading t)
    (rhoX rhoY rhoZ : Fin 3 → Fin t) :
    TensorObj.Isomorphic
      (TensorObj.kron (G.blockSubtensor rhoX)
        (TensorObj.kron
          ((permObjGrading G cyclicPerm).blockSubtensor
            (fun i ↦ rhoY (cyclicPerm.symm i)))
          ((permObjGrading G (cyclicPerm.trans cyclicPerm)).blockSubtensor
            (fun i ↦ rhoZ ((cyclicPerm.trans cyclicPerm).symm i)))))
      ((cyclicTripleGrading G).blockSubtensor
        (cyclicTripleGrade rhoX rhoY rhoZ)) := by
  exact (publicCyclicTripleGrading_blockSubtensor_iso G rhoX rhoY rhoZ).trans
    (gradingOfEq_blockSubtensor_iso
      (cyclicSymmetrization_eq_public_perm T)
      (publicCyclicTripleGrading G)
      (cyclicTripleGrade rhoX rhoY rhoZ)).symm

variable {H volume m W : ℕ}

private theorem permObj_trans_iso_local
    {d : ℕ} (e e' : Equiv.Perm (Fin d)) (X : TensorObj K d) :
    TensorObj.Isomorphic
      (TensorObj.permObj e' (TensorObj.permObj e X))
      (TensorObj.permObj (e.trans e') X) := by
  have ht : (TensorObj.permObj e' (TensorObj.permObj e X)).t =
      (TensorObj.permObj (e.trans e') X).t := by
    exact PiTensorProduct.reindex_reindex e e' X.t
  constructor
  · refine ⟨fun _ ↦ LinearMap.id, ?_⟩
    have hmap := LinearMap.congr_fun
      (PiTensorProduct.map_id
        (R := K) (s := (TensorObj.permObj (e.trans e') X).V))
      (TensorObj.permObj (e.trans e') X).t
    exact hmap.trans ht.symm
  · refine ⟨fun _ ↦ LinearMap.id, ?_⟩
    have hmap := LinearMap.congr_fun
      (PiTensorProduct.map_id
        (R := K) (s := (TensorObj.permObj e' (TensorObj.permObj e X)).V))
      (TensorObj.permObj e' (TensorObj.permObj e X)).t
    exact hmap.trans ht

private theorem MMObj_permObj_cyclic_sq_local (n m p : ℕ) :
    TensorObj.Isomorphic
      (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (MMObj K n m p))
      (MMObj K m p n) := by
  have htrans :=
    (permObj_trans_iso_local cyclicPerm cyclicPerm
      (MMObj K n m p)).symm
  have hfirst := TensorObj.permObj_isomorphic cyclicPerm
    (MME.MMObj_permObj_cyclic (K := K) n m p)
  have hsecond := MME.MMObj_permObj_cyclic (K := K) p n m
  exact htrans.trans (hfirst.trans hsecond)

theorem ctensorOncePermutedComponentIso
    (cert : CTensorOneHOneCertificate T H volume) (h : Fin H) :
    TensorObj.Isomorphic
      (MMObj K (cert.p h) (cert.m h) (cert.n h))
      ((permObjGrading cert.grading cyclicPerm).blockSubtensor
        (fun i ↦ (cTensorOneHOneAddress H h) (cyclicPerm.symm i))) := by
  have hmm := MME.MMObj_permObj_cyclic (K := K)
    (cert.m h) (cert.n h) (cert.p h)
  have hp := TensorObj.permObj_isomorphic cyclicPerm (cert.component h)
  have hg := permObjGrading_blockSubtensor_iso
    cert.grading cyclicPerm (cTensorOneHOneAddress H h)
  exact hmm.symm.trans (hp.trans hg.symm)

theorem ctensorTwicePermutedComponentIso
    (cert : CTensorOneHOneCertificate T H volume) (h : Fin H) :
    TensorObj.Isomorphic
      (MMObj K (cert.n h) (cert.p h) (cert.m h))
      ((permObjGrading cert.grading
          (cyclicPerm.trans cyclicPerm)).blockSubtensor
        (fun i ↦ (cTensorOneHOneAddress H h)
          ((cyclicPerm.trans cyclicPerm).symm i))) := by
  have hmm := MMObj_permObj_cyclic_sq_local (K := K)
    (cert.m h) (cert.n h) (cert.p h)
  have hp := TensorObj.permObj_isomorphic
    (cyclicPerm.trans cyclicPerm) (cert.component h)
  have hg := permObjGrading_blockSubtensor_iso
    cert.grading (cyclicPerm.trans cyclicPerm)
      (cTensorOneHOneAddress H h)
  exact hmm.symm.trans (hp.trans hg.symm)

theorem ctensorCyclicCoordinateBlockIso
    (cert : CTensorOneHOneCertificate T H volume)
    (x y z : Fin H) :
    TensorObj.Isomorphic
      (MMObj K
        (cert.m x * cert.p y * cert.n z)
        (cert.n x * cert.m y * cert.p z)
        (cert.p x * cert.n y * cert.m z))
      ((cyclicTripleGrading cert.grading).blockSubtensor
        (cyclicTripleGrade
          (cTensorOneHOneAddress H x)
          (cTensorOneHOneAddress H y)
          (cTensorOneHOneAddress H z))) := by
  have hcomponents := TensorQ.mul_respects_iso (cert.component x)
    (TensorQ.mul_respects_iso
      (ctensorOncePermutedComponentIso cert y)
      (ctensorTwicePermutedComponentIso cert z))
  have hinner := MMObj_kron_iso (K := K)
    (cert.p y) (cert.m y) (cert.n y)
    (cert.n z) (cert.p z) (cert.m z)
  have hinnerLift := TensorQ.mul_respects_iso
    (TensorObj.Isomorphic.refl
      (MMObj K (cert.m x) (cert.n x) (cert.p x))) hinner
  have houter := MMObj_kron_iso (K := K)
    (cert.m x) (cert.n x) (cert.p x)
    (cert.p y * cert.n z)
    (cert.m y * cert.p z)
    (cert.n y * cert.m z)
  have hmm := hinnerLift.trans houter
  have hblock := cyclicTripleGrading_blockSubtensor_iso cert.grading
    (cTensorOneHOneAddress H x)
    (cTensorOneHOneAddress H y)
    (cTensorOneHOneAddress H z)
  simpa only [mul_assoc] using hmm.symm.trans (hcomponents.trans hblock)

/-- The fine cyclic grade attached to one triple of balanced words at one
mode and one position. -/
def ctensorCyclicAddress
    (words : Fin W ≃
      {w : Fin (H * m) → Fin H // ∀ h,
        Fintype.card {j // w j = h} = m})
    (e : Fin W × Fin W × Fin W)
    (i : Fin 3) (r : Fin (H * m)) :
    Fin ((H + 1) * ((H + 1) * (H + 1))) :=
  cyclicTripleGrade
    (cTensorOneHOneAddress H ((words e.1).1 r))
    (cTensorOneHOneAddress H ((words e.2.1).1 r))
    (cTensorOneHOneAddress H ((words e.2.2).1 r)) i

/-- The paired cyclic address has exactly the three mixed-support collision
constraints required by the balanced-grading certificate. -/
theorem ctensorCyclicAddress_mixed_support
    (cert : CTensorOneHOneCertificate T H volume)
    (words : Fin W ≃
      {w : Fin (H * m) → Fin H // ∀ h,
        Fintype.card {j // w j = h} = m})
    (es : Fin 3 → (Fin W × Fin W × Fin W))
    (hsupp : ∀ r : Fin (H * m),
      (cyclicTripleGrading cert.grading).blockTensor
        (fun i ↦ ctensorCyclicAddress words (es i) i r) ≠ 0) :
    (es 1).2.1 = (es 2).2.1 ∧
      (es 2).2.2 = (es 0).2.2 ∧
      (es 0).1 = (es 1).1 := by
  have hxword : ∀ r : Fin (H * m),
      (words (es 0).1).1 r = (words (es 1).1).1 r := by
    intro r
    let rhoX : Fin 3 → Fin (H + 1) := fun j ↦
      cTensorOneHOneAddress H ((words (es j).1).1 r) j
    let rhoY : Fin 3 → Fin (H + 1) := fun j ↦
      cTensorOneHOneAddress H
        ((words (es (cyclicPerm j)).2.1).1 r) j
    let rhoZ : Fin 3 → Fin (H + 1) := fun j ↦
      cTensorOneHOneAddress H
        ((words (es ((cyclicPerm.trans cyclicPerm) j)).2.2).1 r) j
    have haddr :
        (fun i ↦ ctensorCyclicAddress words (es i) i r) =
          cyclicTripleGrade rhoX rhoY rhoZ := by
      funext i
      simp only [ctensorCyclicAddress, cyclicTripleGrade, rhoX, rhoY, rhoZ]
      rw [cyclicPerm.apply_symm_apply,
        (cyclicPerm.trans cyclicPerm).apply_symm_apply]
    have hblock :
        (cyclicTripleGrading cert.grading).blockTensor
          (cyclicTripleGrade rhoX rhoY rhoZ) ≠ 0 :=
      (blockTensor_ne_zero_congr
        (cyclicTripleGrading cert.grading) haddr).mp (hsupp r)
    have hx : cert.grading.blockTensor rhoX ≠ 0 :=
      cyclicTripleGrading_blockTensor_ne_zero_first
        cert.grading rhoX rhoY rhoZ hblock
    have hxmem : rhoX ∈
        Finset.univ.image (cTensorOneHOneAddress H) := by
      by_contra hn
      exact hx (cert.supported rhoX hn)
    obtain ⟨h, _, hh⟩ := Finset.mem_image.mp hxmem
    have h0 := congrFun hh 0
    have h1 := congrFun hh 1
    have h0' : h = (words (es 0).1).1 r := by
      apply Fin.castSucc_injective H
      simpa [rhoX, cTensorOneHOneAddress] using h0
    have h1' : h = (words (es 1).1).1 r := by
      apply Fin.castSucc_injective H
      simpa [rhoX, cTensorOneHOneAddress] using h1
    exact h0'.symm.trans h1'
  have hyword : ∀ r : Fin (H * m),
      (words (es 1).2.1).1 r = (words (es 2).2.1).1 r := by
    intro r
    let rhoX : Fin 3 → Fin (H + 1) := fun j ↦
      cTensorOneHOneAddress H ((words (es j).1).1 r) j
    let rhoY : Fin 3 → Fin (H + 1) := fun j ↦
      cTensorOneHOneAddress H
        ((words (es (cyclicPerm j)).2.1).1 r) j
    let rhoZ : Fin 3 → Fin (H + 1) := fun j ↦
      cTensorOneHOneAddress H
        ((words (es ((cyclicPerm.trans cyclicPerm) j)).2.2).1 r) j
    have haddr :
        (fun i ↦ ctensorCyclicAddress words (es i) i r) =
          cyclicTripleGrade rhoX rhoY rhoZ := by
      funext i
      simp only [ctensorCyclicAddress, cyclicTripleGrade, rhoX, rhoY, rhoZ]
      rw [cyclicPerm.apply_symm_apply,
        (cyclicPerm.trans cyclicPerm).apply_symm_apply]
    have hblock :
        (cyclicTripleGrading cert.grading).blockTensor
          (cyclicTripleGrade rhoX rhoY rhoZ) ≠ 0 :=
      (blockTensor_ne_zero_congr
        (cyclicTripleGrading cert.grading) haddr).mp (hsupp r)
    have hy : cert.grading.blockTensor rhoY ≠ 0 :=
      cyclicTripleGrading_blockTensor_ne_zero_second
        cert.grading rhoX rhoY rhoZ hblock
    have hymem : rhoY ∈
        Finset.univ.image (cTensorOneHOneAddress H) := by
      by_contra hn
      exact hy (cert.supported rhoY hn)
    obtain ⟨h, _, hh⟩ := Finset.mem_image.mp hymem
    have h0 := congrFun hh 0
    have h1 := congrFun hh 1
    have h0' : h = (words (es 1).2.1).1 r := by
      apply Fin.castSucc_injective H
      simpa [rhoY, cTensorOneHOneAddress, cyclicPerm] using h0
    have h1' : h = (words (es 2).2.1).1 r := by
      apply Fin.castSucc_injective H
      simpa [rhoY, cTensorOneHOneAddress, cyclicPerm] using h1
    exact h0'.symm.trans h1'
  have hzword : ∀ r : Fin (H * m),
      (words (es 2).2.2).1 r = (words (es 0).2.2).1 r := by
    intro r
    let rhoX : Fin 3 → Fin (H + 1) := fun j ↦
      cTensorOneHOneAddress H ((words (es j).1).1 r) j
    let rhoY : Fin 3 → Fin (H + 1) := fun j ↦
      cTensorOneHOneAddress H
        ((words (es (cyclicPerm j)).2.1).1 r) j
    let rhoZ : Fin 3 → Fin (H + 1) := fun j ↦
      cTensorOneHOneAddress H
        ((words (es ((cyclicPerm.trans cyclicPerm) j)).2.2).1 r) j
    have haddr :
        (fun i ↦ ctensorCyclicAddress words (es i) i r) =
          cyclicTripleGrade rhoX rhoY rhoZ := by
      funext i
      simp only [ctensorCyclicAddress, cyclicTripleGrade, rhoX, rhoY, rhoZ]
      rw [cyclicPerm.apply_symm_apply,
        (cyclicPerm.trans cyclicPerm).apply_symm_apply]
    have hblock :
        (cyclicTripleGrading cert.grading).blockTensor
          (cyclicTripleGrade rhoX rhoY rhoZ) ≠ 0 :=
      (blockTensor_ne_zero_congr
        (cyclicTripleGrading cert.grading) haddr).mp (hsupp r)
    have hz : cert.grading.blockTensor rhoZ ≠ 0 :=
      cyclicTripleGrading_blockTensor_ne_zero_third
        cert.grading rhoX rhoY rhoZ hblock
    have hzmem : rhoZ ∈
        Finset.univ.image (cTensorOneHOneAddress H) := by
      by_contra hn
      exact hz (cert.supported rhoZ hn)
    obtain ⟨h, _, hh⟩ := Finset.mem_image.mp hzmem
    have h0 := congrFun hh 0
    have h1 := congrFun hh 1
    have h0' : h = (words (es 2).2.2).1 r := by
      apply Fin.castSucc_injective H
      simpa [rhoZ, cTensorOneHOneAddress, cyclicPerm] using h0
    have h1' : h = (words (es 0).2.2).1 r := by
      apply Fin.castSucc_injective H
      simpa [rhoZ, cTensorOneHOneAddress, cyclicPerm] using h1
    exact h0'.symm.trans h1'
  constructor
  · apply words.injective
    apply Subtype.ext
    funext r
    exact hyword r
  constructor
  · apply words.injective
    apply Subtype.ext
    funext r
    exact hzword r
  · apply words.injective
    apply Subtype.ext
    funext r
    exact hxword r

/-- Every fine address block of the balanced cyclic grading is the matrix
multiplication tensor obtained by multiplying its per-position dimensions. -/
theorem ctensorCyclicAddress_component_iso
    (cert : CTensorOneHOneCertificate T H volume)
    (words : Fin W ≃
      {w : Fin (H * m) → Fin H // ∀ h,
        Fintype.card {j // w j = h} = m})
    (e : Fin W × Fin W × Fin W) :
    TensorObj.Isomorphic
      (MMObj K
        (∏ r, cert.m ((words e.1).1 r) *
          cert.p ((words e.2.1).1 r) * cert.n ((words e.2.2).1 r))
        (∏ r, cert.n ((words e.1).1 r) *
          cert.m ((words e.2.1).1 r) * cert.p ((words e.2.2).1 r))
        (∏ r, cert.p ((words e.1).1 r) *
          cert.n ((words e.2.1).1 r) * cert.m ((words e.2.2).1 r)))
      (gradedAddressBlock (cyclicTripleGrading cert.grading)
        (ctensorCyclicAddress words e)) := by
  let a : Fin (H * m) → ℕ := fun r ↦
    cert.m ((words e.1).1 r) * cert.p ((words e.2.1).1 r) *
      cert.n ((words e.2.2).1 r)
  let b : Fin (H * m) → ℕ := fun r ↦
    cert.n ((words e.1).1 r) * cert.m ((words e.2.1).1 r) *
      cert.p ((words e.2.2).1 r)
  let c : Fin (H * m) → ℕ := fun r ↦
    cert.p ((words e.1).1 r) * cert.n ((words e.2.1).1 r) *
      cert.m ((words e.2.2).1 r)
  have hpoint : ∀ r : Fin (H * m), TensorObj.Isomorphic
      (MMObj K (a r) (b r) (c r))
      ((cyclicTripleGrading cert.grading).blockSubtensor
        (fun i ↦ ctensorCyclicAddress words e i r)) := by
    intro r
    exact ctensorCyclicCoordinateBlockIso cert
      ((words e.1).1 r) ((words e.2.1).1 r) ((words e.2.2).1 r)
  have htransport := mme_kronFin_respects_iso (H * m)
    (fun r ↦ MMObj K (a r) (b r) (c r))
    (fun r ↦ (cyclicTripleGrading cert.grading).blockSubtensor
      (fun i ↦ ctensorCyclicAddress words e i r)) hpoint
  have hmm := mme_kronFin_MMObj_iso (K := K) (H * m) a b c
  simpa only [a, b, c, gradedAddressBlock] using hmm.symm.trans htransport

end MME

theorem solution
    {K : Type u} [Field K]
    {T : TensorObj K 3} {H volume : ℕ}
    (cert : CTensorOneHOneCertificate T H volume)
    (hH : 0 < H) (m W : ℕ)
    (words : Fin W ≃
      {w : Fin (H * m) → Fin H // ∀ h,
        Fintype.card {j // w j = h} = m}) :
    Nonempty (CTensorCyclicBalancedGradingCertificate T H volume m W) := by
  refine ⟨{
    t := (H + 1) * ((H + 1) * (H + 1))
    grading := cyclicTripleGrading cert.grading
    address := ctensorCyclicAddress words
    a := fun e ↦ ∏ r,
      cert.m ((words e.1).1 r) * cert.p ((words e.2.1).1 r) *
        cert.n ((words e.2.2).1 r)
    b := fun e ↦ ∏ r,
      cert.n ((words e.1).1 r) * cert.m ((words e.2.1).1 r) *
        cert.p ((words e.2.2).1 r)
    c := fun e ↦ ∏ r,
      cert.p ((words e.1).1 r) * cert.n ((words e.2.1).1 r) *
        cert.m ((words e.2.2).1 r)
    mixed_support := ctensorCyclicAddress_mixed_support cert words
    component := ctensorCyclicAddress_component_iso cert words
    common_volume := ?_
  }⟩
  intro e
  simpa using
    (mme_Ctensor_cyclic_dimension_products_common_volume cert
      (fun r ↦ (words e.1).1 r)
      (fun r ↦ (words e.2.1).1 r)
      (fun r ↦ (words e.2.2).1 r))
