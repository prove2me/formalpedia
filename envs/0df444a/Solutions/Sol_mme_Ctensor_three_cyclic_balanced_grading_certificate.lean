-- Prove2me | solution 1 for mme_Ctensor_three_cyclic_balanced_grading_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T04:51:48.990695+00:00
-- url     : https://prove2.me/submissions/9d683990-1478-443d-90d7-541ee545370e

import Definitions.Def_CTensorThreeCyclicBalancedGradingCertificate
import Definitions.Def_mme_TypeGrading_permutation
import Definitions.Def_mme_TypeGrading_kron
import Theorems.Thm_mme_TypeGrading_kron_blockSubtensor_iso
import Theorems.Thm_mme_kronFin_respects_iso
import Theorems.Thm_mme_kronFin_MMObj_iso
import Theorems.Thm_mme_MMObj_permObj_cyclic_sq
import Theorems.Thm_mme_Ctensor_three_star_dimension_products_common_volume

open MME TensorProduct PiTensorProduct BigOperators
open MME.TensorObj.TypeGrading

universe u

namespace MME

variable {K : Type u} [Field K]
variable {X Y Z : TensorObj K 3} {t : ℕ}

/-- Encode the three factor grades at one mode. -/
def cyclicTripleGrade
    (rhoX rhoY rhoZ : Fin 3 → Fin t) (i : Fin 3) :
    Fin (t * (t * t)) :=
  finProdFinEquiv
    (rhoX i,
      finProdFinEquiv
        (rhoY (cyclicPerm.symm i),
          rhoZ ((cyclicPerm.trans cyclicPerm).symm i)))

theorem blockTensor_ne_zero_congr
    {A : TensorObj K 3} (G : A.TypeGrading t)
    {rho sigma : Fin 3 → Fin t} (h : rho = sigma) :
    G.blockTensor rho ≠ 0 ↔ G.blockTensor sigma ≠ 0 := by
  subst sigma
  rfl

/-- Product grading on the heterogeneous cyclic product. -/
noncomputable def threeCyclicTripleGrading
    (GX : X.TypeGrading t) (GY : Y.TypeGrading t)
    (GZ : Z.TypeGrading t) :
    (threeStarCyclicProduct X Y Z).TypeGrading (t * (t * t)) :=
  kronGrading GX
    (kronGrading
      (permObjGrading GY cyclicPerm)
      (permObjGrading GZ (cyclicPerm.trans cyclicPerm)))

theorem threeCyclicTripleGrading_blockTensor_ne_zero_first
    (GX : X.TypeGrading t) (GY : Y.TypeGrading t)
    (GZ : Z.TypeGrading t)
    (rhoX rhoY rhoZ : Fin 3 → Fin t)
    (h : (threeCyclicTripleGrading GX GY GZ).blockTensor
      (cyclicTripleGrade rhoX rhoY rhoZ) ≠ 0) :
    GX.blockTensor rhoX ≠ 0 := by
  exact kronGrading_blockTensor_ne_zero_left GX
    (kronGrading
      (permObjGrading GY cyclicPerm)
      (permObjGrading GZ (cyclicPerm.trans cyclicPerm)))
    rhoX
    (fun i ↦ finProdFinEquiv
      (rhoY (cyclicPerm.symm i),
        rhoZ ((cyclicPerm.trans cyclicPerm).symm i))) h

theorem threeCyclicTripleGrading_blockTensor_ne_zero_second
    (GX : X.TypeGrading t) (GY : Y.TypeGrading t)
    (GZ : Z.TypeGrading t)
    (rhoX rhoY rhoZ : Fin 3 → Fin t)
    (h : (threeCyclicTripleGrading GX GY GZ).blockTensor
      (cyclicTripleGrade rhoX rhoY rhoZ) ≠ 0) :
    GY.blockTensor rhoY ≠ 0 := by
  have hinner := kronGrading_blockTensor_ne_zero_right GX
    (kronGrading
      (permObjGrading GY cyclicPerm)
      (permObjGrading GZ (cyclicPerm.trans cyclicPerm)))
    rhoX
    (fun i ↦ finProdFinEquiv
      (rhoY (cyclicPerm.symm i),
        rhoZ ((cyclicPerm.trans cyclicPerm).symm i))) h
  have hperm := kronGrading_blockTensor_ne_zero_left
    (permObjGrading GY cyclicPerm)
    (permObjGrading GZ (cyclicPerm.trans cyclicPerm))
    (fun i ↦ rhoY (cyclicPerm.symm i))
    (fun i ↦ rhoZ ((cyclicPerm.trans cyclicPerm).symm i)) hinner
  intro hy
  apply hperm
  rw [permObjGrading_blockTensor GY cyclicPerm rhoY, hy, map_zero]
  rfl

theorem threeCyclicTripleGrading_blockTensor_ne_zero_third
    (GX : X.TypeGrading t) (GY : Y.TypeGrading t)
    (GZ : Z.TypeGrading t)
    (rhoX rhoY rhoZ : Fin 3 → Fin t)
    (h : (threeCyclicTripleGrading GX GY GZ).blockTensor
      (cyclicTripleGrade rhoX rhoY rhoZ) ≠ 0) :
    GZ.blockTensor rhoZ ≠ 0 := by
  have hinner := kronGrading_blockTensor_ne_zero_right GX
    (kronGrading
      (permObjGrading GY cyclicPerm)
      (permObjGrading GZ (cyclicPerm.trans cyclicPerm)))
    rhoX
    (fun i ↦ finProdFinEquiv
      (rhoY (cyclicPerm.symm i),
        rhoZ ((cyclicPerm.trans cyclicPerm).symm i))) h
  have hperm := kronGrading_blockTensor_ne_zero_right
    (permObjGrading GY cyclicPerm)
    (permObjGrading GZ (cyclicPerm.trans cyclicPerm))
    (fun i ↦ rhoY (cyclicPerm.symm i))
    (fun i ↦ rhoZ ((cyclicPerm.trans cyclicPerm).symm i)) hinner
  intro hz
  apply hperm
  rw [permObjGrading_blockTensor GZ
    (cyclicPerm.trans cyclicPerm) rhoZ, hz, map_zero]
  rfl

/-- One heterogeneous coordinate block is the nested Kronecker product of
the three corresponding factor blocks. -/
theorem threeCyclicTripleGrading_blockSubtensor_iso
    (GX : X.TypeGrading t) (GY : Y.TypeGrading t)
    (GZ : Z.TypeGrading t)
    (rhoX rhoY rhoZ : Fin 3 → Fin t) :
    TensorObj.Isomorphic
      (TensorObj.kron (GX.blockSubtensor rhoX)
        (TensorObj.kron
          ((permObjGrading GY cyclicPerm).blockSubtensor
            (fun i ↦ rhoY (cyclicPerm.symm i)))
          ((permObjGrading GZ
              (cyclicPerm.trans cyclicPerm)).blockSubtensor
            (fun i ↦ rhoZ
              ((cyclicPerm.trans cyclicPerm).symm i)))))
      ((threeCyclicTripleGrading GX GY GZ).blockSubtensor
        (cyclicTripleGrade rhoX rhoY rhoZ)) := by
  let GY' := permObjGrading GY cyclicPerm
  let GZ' := permObjGrading GZ (cyclicPerm.trans cyclicPerm)
  let sy : Fin 3 → Fin t := fun i ↦ rhoY (cyclicPerm.symm i)
  let sz : Fin 3 → Fin t := fun i ↦
    rhoZ ((cyclicPerm.trans cyclicPerm).symm i)
  have hinner := mme_TypeGrading_kron_blockSubtensor_iso GY' GZ' sy sz
  have hlift := TensorQ.mul_respects_iso
    (TensorObj.Isomorphic.refl (GX.blockSubtensor rhoX)) hinner
  have houter := mme_TypeGrading_kron_blockSubtensor_iso
    GX (kronGrading GY' GZ') rhoX
      (fun i ↦ finProdFinEquiv (sy i, sz i))
  exact hlift.trans houter

variable {H volume m W : ℕ}

theorem ctensorOncePermutedComponentIso
    {T : TensorObj K 3}
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
    {T : TensorObj K 3}
    (cert : CTensorOneHOneCertificate T H volume) (h : Fin H) :
    TensorObj.Isomorphic
      (MMObj K (cert.n h) (cert.p h) (cert.m h))
      ((permObjGrading cert.grading
          (cyclicPerm.trans cyclicPerm)).blockSubtensor
        (fun i ↦ (cTensorOneHOneAddress H h)
          ((cyclicPerm.trans cyclicPerm).symm i))) := by
  have hmm := mme_MMObj_permObj_cyclic_sq (K := K)
    (cert.m h) (cert.n h) (cert.p h)
  have hp := TensorObj.permObj_isomorphic
    (cyclicPerm.trans cyclicPerm) (cert.component h)
  have hg := permObjGrading_blockSubtensor_iso
    cert.grading (cyclicPerm.trans cyclicPerm)
      (cTensorOneHOneAddress H h)
  exact hmm.symm.trans (hp.trans hg.symm)

/-- The matrix-product shape of one coordinate block in a heterogeneous
cyclic product. -/
theorem threeCTensorCyclicCoordinateBlockIso
    (certX : CTensorOneHOneCertificate X H volume)
    (certY : CTensorOneHOneCertificate Y H volume)
    (certZ : CTensorOneHOneCertificate Z H volume)
    (x y z : Fin H) :
    TensorObj.Isomorphic
      (MMObj K
        (certX.m x * certY.p y * certZ.n z)
        (certX.n x * certY.m y * certZ.p z)
        (certX.p x * certY.n y * certZ.m z))
      ((threeCyclicTripleGrading
          certX.grading certY.grading certZ.grading).blockSubtensor
        (cyclicTripleGrade
          (cTensorOneHOneAddress H x)
          (cTensorOneHOneAddress H y)
          (cTensorOneHOneAddress H z))) := by
  have hcomponents := TensorQ.mul_respects_iso (certX.component x)
    (TensorQ.mul_respects_iso
      (ctensorOncePermutedComponentIso certY y)
      (ctensorTwicePermutedComponentIso certZ z))
  have hinner := MMObj_kron_iso (K := K)
    (certY.p y) (certY.m y) (certY.n y)
    (certZ.n z) (certZ.p z) (certZ.m z)
  have hinnerLift := TensorQ.mul_respects_iso
    (TensorObj.Isomorphic.refl
      (MMObj K (certX.m x) (certX.n x) (certX.p x))) hinner
  have houter := MMObj_kron_iso (K := K)
    (certX.m x) (certX.n x) (certX.p x)
    (certY.p y * certZ.n z)
    (certY.m y * certZ.p z)
    (certY.n y * certZ.m z)
  have hmm := hinnerLift.trans houter
  have hblock := threeCyclicTripleGrading_blockSubtensor_iso
    certX.grading certY.grading certZ.grading
    (cTensorOneHOneAddress H x)
    (cTensorOneHOneAddress H y)
    (cTensorOneHOneAddress H z)
  simpa only [mul_assoc] using hmm.symm.trans (hcomponents.trans hblock)

/-- The fine address attached to a balanced word triple. -/
def threeCTensorCyclicAddress
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

/-- A nonzero mixed block forces the three balanced-word overlap
equalities.  The three support tests use `certX`, `certY`, and `certZ`
separately. -/
theorem threeCTensorCyclicAddress_mixed_support
    (certX : CTensorOneHOneCertificate X H volume)
    (certY : CTensorOneHOneCertificate Y H volume)
    (certZ : CTensorOneHOneCertificate Z H volume)
    (words : Fin W ≃
      {w : Fin (H * m) → Fin H // ∀ h,
        Fintype.card {j // w j = h} = m})
    (es : Fin 3 → (Fin W × Fin W × Fin W))
    (hsupp : ∀ r : Fin (H * m),
      (threeCyclicTripleGrading
        certX.grading certY.grading certZ.grading).blockTensor
        (fun i ↦ threeCTensorCyclicAddress words (es i) i r) ≠ 0) :
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
        (fun i ↦ threeCTensorCyclicAddress words (es i) i r) =
          cyclicTripleGrade rhoX rhoY rhoZ := by
      funext i
      simp only [threeCTensorCyclicAddress, cyclicTripleGrade,
        rhoX, rhoY, rhoZ]
      rw [cyclicPerm.apply_symm_apply,
        (cyclicPerm.trans cyclicPerm).apply_symm_apply]
    have hblock :
        (threeCyclicTripleGrading
          certX.grading certY.grading certZ.grading).blockTensor
          (cyclicTripleGrade rhoX rhoY rhoZ) ≠ 0 :=
      (blockTensor_ne_zero_congr
        (threeCyclicTripleGrading
          certX.grading certY.grading certZ.grading) haddr).mp
        (hsupp r)
    have hx : certX.grading.blockTensor rhoX ≠ 0 :=
      threeCyclicTripleGrading_blockTensor_ne_zero_first
        certX.grading certY.grading certZ.grading
        rhoX rhoY rhoZ hblock
    have hxmem : rhoX ∈
        Finset.univ.image (cTensorOneHOneAddress H) := by
      by_contra hn
      exact hx (certX.supported rhoX hn)
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
        (fun i ↦ threeCTensorCyclicAddress words (es i) i r) =
          cyclicTripleGrade rhoX rhoY rhoZ := by
      funext i
      simp only [threeCTensorCyclicAddress, cyclicTripleGrade,
        rhoX, rhoY, rhoZ]
      rw [cyclicPerm.apply_symm_apply,
        (cyclicPerm.trans cyclicPerm).apply_symm_apply]
    have hblock :
        (threeCyclicTripleGrading
          certX.grading certY.grading certZ.grading).blockTensor
          (cyclicTripleGrade rhoX rhoY rhoZ) ≠ 0 :=
      (blockTensor_ne_zero_congr
        (threeCyclicTripleGrading
          certX.grading certY.grading certZ.grading) haddr).mp
        (hsupp r)
    have hy : certY.grading.blockTensor rhoY ≠ 0 :=
      threeCyclicTripleGrading_blockTensor_ne_zero_second
        certX.grading certY.grading certZ.grading
        rhoX rhoY rhoZ hblock
    have hymem : rhoY ∈
        Finset.univ.image (cTensorOneHOneAddress H) := by
      by_contra hn
      exact hy (certY.supported rhoY hn)
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
        (fun i ↦ threeCTensorCyclicAddress words (es i) i r) =
          cyclicTripleGrade rhoX rhoY rhoZ := by
      funext i
      simp only [threeCTensorCyclicAddress, cyclicTripleGrade,
        rhoX, rhoY, rhoZ]
      rw [cyclicPerm.apply_symm_apply,
        (cyclicPerm.trans cyclicPerm).apply_symm_apply]
    have hblock :
        (threeCyclicTripleGrading
          certX.grading certY.grading certZ.grading).blockTensor
          (cyclicTripleGrade rhoX rhoY rhoZ) ≠ 0 :=
      (blockTensor_ne_zero_congr
        (threeCyclicTripleGrading
          certX.grading certY.grading certZ.grading) haddr).mp
        (hsupp r)
    have hz : certZ.grading.blockTensor rhoZ ≠ 0 :=
      threeCyclicTripleGrading_blockTensor_ne_zero_third
        certX.grading certY.grading certZ.grading
        rhoX rhoY rhoZ hblock
    have hzmem : rhoZ ∈
        Finset.univ.image (cTensorOneHOneAddress H) := by
      by_contra hn
      exact hz (certZ.supported rhoZ hn)
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

/-- The full address block is the Kronecker product of its per-position
matrix products. -/
theorem threeCTensorCyclicAddress_component_iso
    (certX : CTensorOneHOneCertificate X H volume)
    (certY : CTensorOneHOneCertificate Y H volume)
    (certZ : CTensorOneHOneCertificate Z H volume)
    (words : Fin W ≃
      {w : Fin (H * m) → Fin H // ∀ h,
        Fintype.card {j // w j = h} = m})
    (e : Fin W × Fin W × Fin W) :
    TensorObj.Isomorphic
      (MMObj K
        (∏ r, certX.m ((words e.1).1 r) *
          certY.p ((words e.2.1).1 r) *
          certZ.n ((words e.2.2).1 r))
        (∏ r, certX.n ((words e.1).1 r) *
          certY.m ((words e.2.1).1 r) *
          certZ.p ((words e.2.2).1 r))
        (∏ r, certX.p ((words e.1).1 r) *
          certY.n ((words e.2.1).1 r) *
          certZ.m ((words e.2.2).1 r)))
      (gradedAddressBlock
        (threeCyclicTripleGrading
          certX.grading certY.grading certZ.grading)
        (threeCTensorCyclicAddress words e)) := by
  let a : Fin (H * m) → ℕ := fun r ↦
    certX.m ((words e.1).1 r) *
      certY.p ((words e.2.1).1 r) *
      certZ.n ((words e.2.2).1 r)
  let b : Fin (H * m) → ℕ := fun r ↦
    certX.n ((words e.1).1 r) *
      certY.m ((words e.2.1).1 r) *
      certZ.p ((words e.2.2).1 r)
  let c : Fin (H * m) → ℕ := fun r ↦
    certX.p ((words e.1).1 r) *
      certY.n ((words e.2.1).1 r) *
      certZ.m ((words e.2.2).1 r)
  have hpoint : ∀ r : Fin (H * m), TensorObj.Isomorphic
      (MMObj K (a r) (b r) (c r))
      ((threeCyclicTripleGrading
        certX.grading certY.grading certZ.grading).blockSubtensor
        (fun i ↦ threeCTensorCyclicAddress words e i r)) := by
    intro r
    exact threeCTensorCyclicCoordinateBlockIso certX certY certZ
      ((words e.1).1 r) ((words e.2.1).1 r) ((words e.2.2).1 r)
  have htransport := mme_kronFin_respects_iso (H * m)
    (fun r ↦ MMObj K (a r) (b r) (c r))
    (fun r ↦ (threeCyclicTripleGrading
      certX.grading certY.grading certZ.grading).blockSubtensor
      (fun i ↦ threeCTensorCyclicAddress words e i r)) hpoint
  have hmm := mme_kronFin_MMObj_iso (K := K) (H * m) a b c
  simpa only [a, b, c, gradedAddressBlock] using hmm.symm.trans htransport

theorem mme_Ctensor_three_cyclic_balanced_grading_certificate_exact_scratch
    (certX : CTensorOneHOneCertificate X H volume)
    (certY : CTensorOneHOneCertificate Y H volume)
    (certZ : CTensorOneHOneCertificate Z H volume)
    (hH : 0 < H) (m W : ℕ)
    (words : Fin W ≃
      {w : Fin (H * m) → Fin H // ∀ h,
        Fintype.card {j // w j = h} = m}) :
    Nonempty
      (CTensorThreeCyclicBalancedGradingCertificate
        X Y Z H volume m W) := by
  refine ⟨{
    t := (H + 1) * ((H + 1) * (H + 1))
    grading := threeCyclicTripleGrading
      certX.grading certY.grading certZ.grading
    address := threeCTensorCyclicAddress words
    a := fun e ↦ ∏ r,
      certX.m ((words e.1).1 r) * certY.p ((words e.2.1).1 r) *
        certZ.n ((words e.2.2).1 r)
    b := fun e ↦ ∏ r,
      certX.n ((words e.1).1 r) * certY.m ((words e.2.1).1 r) *
        certZ.p ((words e.2.2).1 r)
    c := fun e ↦ ∏ r,
      certX.p ((words e.1).1 r) * certY.n ((words e.2.1).1 r) *
        certZ.m ((words e.2.2).1 r)
    mixed_support := threeCTensorCyclicAddress_mixed_support
      certX certY certZ words
    component := threeCTensorCyclicAddress_component_iso
      certX certY certZ words
    common_volume := ?_
  }⟩
  intro e
  simpa using
    (mme_Ctensor_three_star_dimension_products_common_volume
      certX certY certZ
      (fun r ↦ (words e.1).1 r)
      (fun r ↦ (words e.2.1).1 r)
      (fun r ↦ (words e.2.2).1 r))

end MME

theorem solution
    {K : Type u} [Field K]
    {X Y Z : TensorObj K 3} {H volume : ℕ}
    (certX : CTensorOneHOneCertificate X H volume)
    (certY : CTensorOneHOneCertificate Y H volume)
    (certZ : CTensorOneHOneCertificate Z H volume)
    (hH : 0 < H) (m W : ℕ)
    (words : Fin W ≃
      {w : Fin (H * m) → Fin H // ∀ h,
        Fintype.card {j // w j = h} = m}) :
    Nonempty
      (CTensorThreeCyclicBalancedGradingCertificate
        X Y Z H volume m W) := by
  exact MME.mme_Ctensor_three_cyclic_balanced_grading_certificate_exact_scratch
    certX certY certZ hH m W words
