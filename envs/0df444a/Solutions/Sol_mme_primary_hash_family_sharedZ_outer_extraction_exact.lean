-- Prove2me | solution 1 for mme_primary_hash_family_sharedZ_outer_extraction_exact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T08:10:40.482129+00:00
-- url     : https://prove2.me/submissions/3439c236-58a7-469b-b4ce-f82dd43ebec5

import Definitions.Def_mme_coupled_Ctensor_outer_extraction_data

open MME PiTensorProduct BigOperators

universe u

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace CoupledCTensorPackaging

variable {K : Type u} [Field K]

theorem outerExtraction_interchange_tprod
    {V W : Fin 3 → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (v : ∀ i, V i) (w : ∀ i, W i) :
    interchange (tprod K v) (tprod K w) =
      tprod K (fun i => v i ⊗ₜ[K] w i) := by
  show (interchange (tprod K v)) (tprod K w) = _
  unfold interchange
  rw [PiTensorProduct.lift.tprod]
  show (PiTensorProduct.lift (interchangeInner v)) (tprod K w) = _
  rw [PiTensorProduct.lift.tprod]
  rfl

theorem outerExtraction_map_interchange
    {V₁ V₂ V₃ V₄ : Fin 3 → Type u}
    [∀ i, AddCommGroup (V₁ i)] [∀ i, Module K (V₁ i)]
    [∀ i, AddCommGroup (V₂ i)] [∀ i, Module K (V₂ i)]
    [∀ i, AddCommGroup (V₃ i)] [∀ i, Module K (V₃ i)]
    [∀ i, AddCommGroup (V₄ i)] [∀ i, Module K (V₄ i)]
    (f : ∀ i, V₁ i →ₗ[K] V₃ i) (g : ∀ i, V₂ i →ₗ[K] V₄ i)
    (t₁ : PiTensorProduct K V₁) (t₂ : PiTensorProduct K V₂) :
    PiTensorProduct.map (fun i => TensorProduct.map (f i) (g i))
        (interchange t₁ t₂) =
      interchange (PiTensorProduct.map f t₁)
        (PiTensorProduct.map g t₂) := by
  induction t₁ using PiTensorProduct.induction_on with
  | smul_tprod c v =>
      induction t₂ using PiTensorProduct.induction_on with
      | smul_tprod c' v' =>
          simp only [map_smul, LinearMap.smul_apply]
          rw [outerExtraction_interchange_tprod, PiTensorProduct.map_tprod,
            PiTensorProduct.map_tprod, PiTensorProduct.map_tprod,
            outerExtraction_interchange_tprod]
          simp only [TensorProduct.map_tmul]
      | add x y ih₁ ih₂ =>
          simp only [map_add, LinearMap.add_apply, ih₁, ih₂]
  | add x y ih₁ ih₂ =>
      simp only [map_add, LinearMap.add_apply, ih₁, ih₂]

theorem map_addressProj_outer
    {T : TensorObj K 3} {t R : ℕ}
    (grading : T.TypeGrading t) (address : Fin 3 → Fin R → Fin t) :
    PiTensorProduct.map (gradedAddressProj grading R address)
        (T.kronPow R).t =
      (gradedAddressBlock grading address).t := by
  induction R with
  | zero =>
      change PiTensorProduct.map (fun _ => LinearMap.id)
          (TensorObj.oneObj : TensorObj K 3).t =
        (TensorObj.oneObj : TensorObj K 3).t
      rw [PiTensorProduct.map_id]
      rfl
  | succ R ih =>
      change PiTensorProduct.map
          (fun i => TensorProduct.map
            (grading.blockProj i (address i 0))
            (gradedAddressProj grading R
              (fun i' j => address i' j.succ) i))
          (interchange T.t (T.kronPow R).t) =
        interchange
          (grading.blockTensor (fun i => address i 0))
          (gradedAddressBlock grading
            (fun i j => address i j.succ)).t
      rw [outerExtraction_map_interchange]
      unfold TensorObj.TypeGrading.blockTensor
      rw [ih]

theorem gradedAddressBlock_t_eq_zero_of_coord_outer
    {T : TensorObj K 3} {t R : ℕ}
    (grading : T.TypeGrading t) (address : Fin 3 → Fin R → Fin t)
    (r : Fin R)
    (hr : grading.blockTensor (fun i => address i r) = 0) :
    (gradedAddressBlock grading address).t = 0 := by
  induction R with
  | zero => exact Fin.elim0 r
  | succ R ih =>
      refine Fin.cases
        (motive := fun r =>
          grading.blockTensor (fun i => address i r) = 0 →
            (gradedAddressBlock grading address).t = 0)
        ?_ (fun r' => ?_) r hr
      · intro hr0
        change interchange (grading.blockTensor (fun i => address i 0))
            (gradedAddressBlock grading
              (fun i j => address i j.succ)).t = 0
        rw [hr0]
        simp only [map_zero, LinearMap.zero_apply]
      · intro hr'
        change interchange (grading.blockTensor (fun i => address i 0))
            (gradedAddressBlock grading
              (fun i j => address i j.succ)).t = 0
        have htail :
            (gradedAddressBlock grading
              (fun i j => address i j.succ)).t = 0 :=
          ih (fun i j => address i j.succ) r' hr'
        rw [htail]
        exact LinearMap.map_zero _

theorem map_sum_modes_dependent
    {J : Fin 3 → Type*} [∀ i, Fintype (J i)]
    {V W : Fin 3 → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (f : ∀ i, J i → V i →ₗ[K] W i)
    (x : PiTensorProduct K V) :
    PiTensorProduct.map (fun i => ∑ j, f i j) x =
      ∑ js : ∀ i, J i,
        PiTensorProduct.map (fun i => f i (js i)) x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c v =>
      simp only [map_smul, LinearMap.smul_apply, Finset.sum_smul]
      congr 1
      simp only [PiTensorProduct.map_tprod, LinearMap.coe_sum,
        Finset.sum_apply]
      rw [MultilinearMap.map_sum (PiTensorProduct.tprod K) _]
      rw [Finset.smul_sum]
  | add x y ihx ihy =>
      simp only [map_add, ihx, ihy, Finset.sum_add_distrib]

theorem bigAdd_t_eq_sum_slot_outer :
    ∀ (k : ℕ) (B : Fin k → TensorObj K 3),
      (TensorObj.bigAdd B).t =
        ∑ j : Fin k,
          PiTensorProduct.map
            (fun i => gradedBigAddSlot k B j i) (B j).t
  | 0, _ => by
      change (TensorObj.zeroObj : TensorObj K 3).t = ∑ j : Fin 0, _
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
      rfl
  | 1, B => by
      change (B 0).t =
        ∑ j : Fin 1,
          PiTensorProduct.map
            (fun i => gradedBigAddSlot 1 B j i) (B j).t
      rw [Fin.sum_univ_one]
      change (B 0).t =
        PiTensorProduct.map (fun _ => LinearMap.id) (B 0).t
      rw [PiTensorProduct.map_id]
      rfl
  | n + 2, B => by
      change PiTensorProduct.map (fun i =>
              LinearMap.inl K ((B 0).V i)
                ((TensorObj.bigAdd (fun j => B j.succ)).V i)) (B 0).t +
          PiTensorProduct.map (fun i =>
              LinearMap.inr K ((B 0).V i)
                ((TensorObj.bigAdd (fun j => B j.succ)).V i))
            (TensorObj.bigAdd (fun j => B j.succ)).t =
        ∑ j : Fin (n + 2),
          PiTensorProduct.map
            (fun i => gradedBigAddSlot (n + 2) B j i) (B j).t
      rw [Fin.sum_univ_succ]
      rw [bigAdd_t_eq_sum_slot_outer (n + 1) (fun j => B j.succ)]
      congr 1
      rw [map_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
      rfl

variable {T : TensorObj K 3} (grading : T.TypeGrading 3)
variable {N L G A H : ℕ}

theorem outerMixedSupported_implies_diagonal
    (family : CWQ6PrimaryHashFamily N L G A H)
    (js : ∀ i : Fin 3, outerChoiceType (A := A) (H := H) i)
    (hsupported : CWQ6CoupledCoordinatewiseSupported
      (outerMixedAddress family js)) :
    ∃ a : Fin A, ∃ h : Fin H,
      js = outerDiagonalChoice a h := by
  have hsupported' :
      CWQ6CoupledCoordinatewiseSupported
        (cwQ6CoupledMixedAddress
          (family.entry (js 0)).1
          (family.entry (js 1)).1
          (family.entry (js 2, firstFiberIndex family)).1) := by
    exact hsupported
  obtain ⟨hxy, hza⟩ := family.induced
    (js 0) (js 1) (js 2, firstFiberIndex family) hsupported'
  refine ⟨(js 0).1, (js 0).2, ?_⟩
  funext i
  fin_cases i
  · rfl
  · exact hxy.symm
  · exact hza.symm

theorem outerMixedSupported_of_all_nonzero
    (hSupport : ∀ σ : Fin 3 → Fin 3,
      σ ≠ ![0, 0, 0] → σ ≠ ![1, 1, 1] →
      σ ≠ ![0, 1, 2] → σ ≠ ![1, 0, 2] →
      grading.blockTensor σ = 0)
    (family : CWQ6PrimaryHashFamily N L G A H)
    (js : ∀ i : Fin 3, outerChoiceType (A := A) (H := H) i)
    (hall : ∀ r : Fin (2 * N),
      grading.blockTensor (fun i => outerMixedAddress family js i r) ≠ 0) :
    CWQ6CoupledCoordinatewiseSupported (outerMixedAddress family js) := by
  intro r
  let σ : Fin 3 → Fin 3 := fun i => outerMixedAddress family js i r
  by_cases h000 : σ = ![0, 0, 0]
  · left
    simpa [σ] using congrArg (fun f : Fin 3 → Fin 3 =>
      (f 0, f 1, f 2)) h000
  by_cases h111 : σ = ![1, 1, 1]
  · right; left
    simpa [σ] using congrArg (fun f : Fin 3 → Fin 3 =>
      (f 0, f 1, f 2)) h111
  by_cases h012 : σ = ![0, 1, 2]
  · right; right; left
    simpa [σ] using congrArg (fun f : Fin 3 → Fin 3 =>
      (f 0, f 1, f 2)) h012
  by_cases h102 : σ = ![1, 0, 2]
  · right; right; right
    simpa [σ] using congrArg (fun f : Fin 3 → Fin 3 =>
      (f 0, f 1, f 2)) h102
  exact (hall r (hSupport σ h000 h111 h012 h102)).elim

theorem outerSummand_factor
    (family : CWQ6PrimaryHashFamily N L G A H)
    (js : ∀ i : Fin 3, outerChoiceType (A := A) (H := H) i) :
    (fun i => outerExtractionSummand grading family i (js i)) =
      fun i => (outerTargetInclusion grading family js i).comp
        (gradedAddressProj grading (2 * N)
          (outerChosenAddress family js i) i) := by
  funext i
  fin_cases i <;> apply LinearMap.ext <;> intro x <;> rfl

theorem outerProjection_eq_zero_of_coord
    {R : ℕ} (addresses : Fin 3 → Fin 3 → Fin R → Fin 3)
    (r : Fin R)
    (hr : grading.blockTensor (fun i => addresses i i r) = 0) :
    PiTensorProduct.map
        (fun i => gradedAddressProj grading R (addresses i) i)
        (T.kronPow R).t = 0 := by
  induction R with
  | zero => exact Fin.elim0 r
  | succ R ih =>
      refine Fin.cases
        (motive := fun r =>
          grading.blockTensor (fun i => addresses i i r) = 0 →
          PiTensorProduct.map
              (fun i => gradedAddressProj grading (R + 1)
                (addresses i) i)
              (T.kronPow (R + 1)).t = 0)
        ?_ (fun r' => ?_) r hr
      · intro hr0
        simp only [gradedAddressProj, TensorObj.kronPow]
        change PiTensorProduct.map
            (fun i => TensorProduct.map
              (grading.blockProj i (addresses i i 0))
              (gradedAddressProj grading R
                (fun i' s => addresses i i' s.succ) i))
            (interchange T.t (T.kronPow R).t) = 0
        rw [outerExtraction_map_interchange]
        have hfirst :
            PiTensorProduct.map
                (fun i => grading.blockProj i (addresses i i 0)) T.t =
              grading.blockTensor (fun i => addresses i i 0) := rfl
        rw [hfirst, hr0]
        simp only [map_zero, LinearMap.zero_apply]
      · intro hr'
        simp only [gradedAddressProj, TensorObj.kronPow]
        change PiTensorProduct.map
            (fun i => TensorProduct.map
              (grading.blockProj i (addresses i i 0))
              (gradedAddressProj grading R
                (fun i' s => addresses i i' s.succ) i))
            (interchange T.t (T.kronPow R).t) = 0
        rw [outerExtraction_map_interchange]
        have htail := ih
          (fun i i' s => addresses i i' s.succ)
          r' hr'
        rw [htail]
        exact LinearMap.map_zero _

theorem outerMixedProjection_eq_zero_of_nondiagonal
    (hSupport : ∀ σ : Fin 3 → Fin 3,
      σ ≠ ![0, 0, 0] → σ ≠ ![1, 1, 1] →
      σ ≠ ![0, 1, 2] → σ ≠ ![1, 0, 2] →
      grading.blockTensor σ = 0)
    (family : CWQ6PrimaryHashFamily N L G A H)
    (js : ∀ i : Fin 3, outerChoiceType (A := A) (H := H) i)
    (hjs : ∀ a : Fin A, ∀ h : Fin H,
      js ≠ outerDiagonalChoice a h) :
    PiTensorProduct.map
        (fun i => gradedAddressProj grading (2 * N)
          (outerChosenAddress family js i) i)
        (T.kronPow (2 * N)).t = 0 := by
  have hbad : ∃ r : Fin (2 * N),
      grading.blockTensor (fun i => outerMixedAddress family js i r) = 0 := by
    by_contra h
    have hall : ∀ r : Fin (2 * N),
        grading.blockTensor
          (fun i => outerMixedAddress family js i r) ≠ 0 := by
      intro r hr
      exact h ⟨r, hr⟩
    obtain ⟨a, h0, hdiag⟩ := outerMixedSupported_implies_diagonal
      family js (outerMixedSupported_of_all_nonzero
        grading hSupport family js hall)
    exact hjs a h0 hdiag
  obtain ⟨r, hr⟩ := hbad
  exact outerProjection_eq_zero_of_coord grading
    (fun i => outerChosenAddress family js i) r hr

theorem outerMappedTerm_eq_zero_of_nondiagonal
    (hSupport : ∀ σ : Fin 3 → Fin 3,
      σ ≠ ![0, 0, 0] → σ ≠ ![1, 1, 1] →
      σ ≠ ![0, 1, 2] → σ ≠ ![1, 0, 2] →
      grading.blockTensor σ = 0)
    (family : CWQ6PrimaryHashFamily N L G A H)
    (js : ∀ i : Fin 3, outerChoiceType (A := A) (H := H) i)
    (hjs : ∀ a : Fin A, ∀ h : Fin H,
      js ≠ outerDiagonalChoice a h) :
    PiTensorProduct.map
        (fun i => outerExtractionSummand grading family i (js i))
        (T.kronPow (2 * N)).t = 0 := by
  rw [outerSummand_factor grading family js]
  rw [PiTensorProduct.map_comp, LinearMap.comp_apply]
  rw [outerMixedProjection_eq_zero_of_nondiagonal
    grading hSupport family js hjs]
  exact LinearMap.map_zero _

theorem modeEquiv_comp_addressProj
    {R : ℕ} (address address' : Fin 3 → Fin R → Fin 3)
    (i : Fin 3) (hi : address i = address' i) :
    (gradedAddressBlockModeEquiv grading R address address' i hi).toLinearMap.comp
        (gradedAddressProj grading R address i) =
      gradedAddressProj grading R address' i := by
  induction R with
  | zero => rfl
  | succ R ih =>
      simp only [gradedAddressBlockModeEquiv, gradedAddressProj]
      apply TensorProduct.ext'
      intro x y
      change
        (LinearEquiv.ofEq
          (grading.classOf i (address i 0))
          (grading.classOf i (address' i 0)) _
          (grading.blockProj i (address i 0) x)) ⊗ₜ[K]
            (gradedAddressBlockModeEquiv grading R
              (fun i' j => address i' j.succ)
              (fun i' j => address' i' j.succ) i _)
              (gradedAddressProj grading R
                (fun i' j => address i' j.succ) i y) =
          (grading.blockProj i (address' i 0) x) ⊗ₜ[K]
            gradedAddressProj grading R
              (fun i' j => address' i' j.succ) i y
      congr 1
      · have h0 : address i 0 = address' i 0 := congrFun hi 0
        apply Subtype.ext
        change
          ((grading.blockProj i (address i 0) x :
              grading.classOf i (address i 0)) : T.V i) =
            ((grading.blockProj i (address' i 0) x :
              grading.classOf i (address' i 0)) : T.V i)
        exact congrArg
          (fun r : Fin 3 =>
            ((grading.blockProj i r x : grading.classOf i r) : T.V i)) h0
      · have htail :
            (fun j : Fin R => address i j.succ) =
              (fun j : Fin R => address' i j.succ) := by
          funext j
          exact congrFun hi j.succ
        have hih := ih
          (fun i' j => address i' j.succ)
          (fun i' j => address' i' j.succ) htail
        exact LinearMap.congr_fun hih y

theorem outerDiagonalMappedTerm
    (family : CWQ6PrimaryHashFamily N L G A H)
    (a : Fin A) (h : Fin H) :
    PiTensorProduct.map
        (fun i => outerExtractionSummand grading family i
          (outerDiagonalChoice a h i))
        (T.kronPow (2 * N)).t =
      PiTensorProduct.map
        (fun i => gradedBigAddSlot A (starObj grading family) a i)
        (PiTensorProduct.map (componentInclusion grading family a h)
          (componentObj grading family a h).t) := by
  have hmaps :
      (fun i => outerExtractionSummand grading family i
        (outerDiagonalChoice a h i)) =
      fun i =>
        (gradedBigAddSlot A (starObj grading family) a i).comp
          ((componentInclusion grading family a h i).comp
            (gradedAddressProj grading (2 * N)
              (componentAddress family a h) i)) := by
    funext i
    fin_cases i
    · rfl
    · rfl
    · apply LinearMap.ext
      intro x
      change (gradedBigAddSlot A (starObj grading family) a 2)
          (gradedAddressProj grading (2 * N)
            (componentAddress family a (firstFiberIndex family)) 2 x) =
        (gradedBigAddSlot A (starObj grading family) a 2)
          (componentInclusion grading family a h 2
            (gradedAddressProj grading (2 * N)
              (componentAddress family a h) 2 x))
      congr 1
      have hshared :
          (componentInclusion grading family a h 2).comp
              (gradedAddressProj grading (2 * N)
                (componentAddress family a h) 2) =
            gradedAddressProj grading (2 * N)
              (componentAddress family a (firstFiberIndex family)) 2 := by
        change (componentZEquiv grading family a h).toLinearMap.comp
            (gradedAddressProj grading (2 * N)
              (componentAddress family a h) 2) = _
        exact modeEquiv_comp_addressProj
          grading (componentAddress family a h)
          (componentAddress family a (firstFiberIndex family)) 2 rfl
      exact congrArg (fun f => f x) hshared.symm
  rw [hmaps]
  have hsplit :
      PiTensorProduct.map
          (fun i => (gradedBigAddSlot A (starObj grading family) a i).comp
            ((componentInclusion grading family a h i).comp
              (gradedAddressProj grading (2 * N)
                (componentAddress family a h) i)))
          (T.kronPow (2 * N)).t =
        PiTensorProduct.map
          (fun i => gradedBigAddSlot A (starObj grading family) a i)
          (PiTensorProduct.map
            (fun i => (componentInclusion grading family a h i).comp
              (gradedAddressProj grading (2 * N)
                (componentAddress family a h) i))
            (T.kronPow (2 * N)).t) :=
    congrFun (congrArg DFunLike.coe
      (PiTensorProduct.map_comp
        (fun i => gradedBigAddSlot A (starObj grading family) a i)
        (fun i => (componentInclusion grading family a h i).comp
          (gradedAddressProj grading (2 * N)
            (componentAddress family a h) i)))) _
  refine hsplit.trans (congrArg (fun z => PiTensorProduct.map
    (fun i => gradedBigAddSlot A (starObj grading family) a i) z) ?_)
  have hinner :
      PiTensorProduct.map
          (fun i => (componentInclusion grading family a h i).comp
            (gradedAddressProj grading (2 * N)
              (componentAddress family a h) i))
          (T.kronPow (2 * N)).t =
        PiTensorProduct.map (componentInclusion grading family a h)
          (PiTensorProduct.map
            (fun i => gradedAddressProj grading (2 * N)
              (componentAddress family a h) i)
            (T.kronPow (2 * N)).t) :=
    congrFun (congrArg DFunLike.coe
      (PiTensorProduct.map_comp
        (componentInclusion grading family a h)
        (fun i => gradedAddressProj grading (2 * N)
          (componentAddress family a h) i))) _
  exact hinner.trans (congrArg
    (fun z => PiTensorProduct.map
      (componentInclusion grading family a h) z)
    (map_addressProj_outer grading (componentAddress family a h)))

theorem bigAdd_starObj_t_eq_sum_components_outer
    (family : CWQ6PrimaryHashFamily N L G A H) :
    (TensorObj.bigAdd (starObj grading family)).t =
      ∑ p : Fin A × Fin H,
        PiTensorProduct.map
          (fun i => gradedBigAddSlot A (starObj grading family) p.1 i)
          (PiTensorProduct.map
            (componentInclusion grading family p.1 p.2)
            (componentObj grading family p.1 p.2).t) := by
  rw [bigAdd_t_eq_sum_slot_outer]
  simp_rw [show ∀ a : Fin A,
      (starObj grading family a).t =
        ∑ h : Fin H,
          PiTensorProduct.map
            (componentInclusion grading family a h)
            (componentObj grading family a h).t by
    intro a
    rfl]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  calc
    _ = ∑ h : Fin H,
        PiTensorProduct.map
          (fun i => gradedBigAddSlot A (starObj grading family) a i)
          (PiTensorProduct.map
            (componentInclusion grading family a h)
            (componentObj grading family a h).t) := by
      exact map_sum
        (PiTensorProduct.map
          (fun i => gradedBigAddSlot A (starObj grading family) a i))
        (fun h : Fin H =>
          PiTensorProduct.map
            (componentInclusion grading family a h)
            (componentObj grading family a h).t)
        Finset.univ
    _ = _ := by rfl

theorem outerExtraction_exact_internal
    (family : CWQ6PrimaryHashFamily N L G A H)
    (hSupport : ∀ σ : Fin 3 → Fin 3,
      σ ≠ ![0, 0, 0] → σ ≠ ![1, 1, 1] →
      σ ≠ ![0, 1, 2] → σ ≠ ![1, 0, 2] →
      grading.blockTensor σ = 0) :
    PiTensorProduct.map (outerExtractionMap grading family)
        (T.kronPow (2 * N)).t =
      (TensorObj.bigAdd (starObj grading family)).t ∧
    outerExtractionMap grading family 2 =
      ∑ a : Fin A,
        (gradedBigAddSlot A (starObj grading family) a 2).comp
          (gradedAddressProj grading (2 * N)
            (componentAddress family a (firstFiberIndex family)) 2) := by
  classical
  constructor
  · unfold outerExtractionMap
    rw [map_sum_modes_dependent]
    let term := fun js :
        (∀ i : Fin 3, outerChoiceType (A := A) (H := H) i) =>
      PiTensorProduct.map
        (fun i => outerExtractionSummand grading family i (js i))
        (T.kronPow (2 * N)).t
    let componentTerm := fun p : Fin A × Fin H =>
      PiTensorProduct.map
        (fun i => gradedBigAddSlot A (starObj grading family) p.1 i)
        (PiTensorProduct.map (componentInclusion grading family p.1 p.2)
          (componentObj grading family p.1 p.2).t)
    change (∑ js, term js) = (TensorObj.bigAdd (starObj grading family)).t
    have hsplit :
        (∑ js, term js) =
          (∑ js ∈ outerDiagonalChoicesCore (A := A) (H := H),
            term js) := by
      symm
      apply Finset.sum_subset
      · exact Finset.subset_univ _
      · intro js _ hnot
        apply outerMappedTerm_eq_zero_of_nondiagonal
          grading hSupport family js
        intro a h heq
        apply hnot
        exact Finset.mem_image.mpr
          ⟨(a, h), Finset.mem_univ (a, h), heq.symm⟩
    have hreindex :
        (∑ js ∈ outerDiagonalChoicesCore (A := A) (H := H),
            term js) =
          ∑ p : Fin A × Fin H, componentTerm p := by
      refine (Finset.sum_bij
        (fun p (_ : p ∈ (Finset.univ : Finset (Fin A × Fin H))) =>
          outerDiagonalChoice p.1 p.2)
        (fun p _ => Finset.mem_image.mpr
          ⟨p, Finset.mem_univ p, rfl⟩)
        ?_ ?_ ?_).symm
      · intro p _ q _ hpq
        exact congrFun hpq 0
      · intro js hjs
        obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hjs
        exact ⟨p, Finset.mem_univ p, hp⟩
      · intro p _
        exact (outerDiagonalMappedTerm
          grading family p.1 p.2).symm
    rw [hsplit, hreindex]
    exact (bigAdd_starObj_t_eq_sum_components_outer
      grading family).symm
  · rfl

end CoupledCTensorPackaging

open CoupledCTensorPackaging

theorem solution
    {K : Type u} [Field K]
    {T : TensorObj K 3} (grading : T.TypeGrading 3)
    {N L G A H : ℕ}
    (family : CWQ6PrimaryHashFamily N L G A H)
    (hSupport : ∀ σ : Fin 3 → Fin 3,
      σ ≠ ![0, 0, 0] → σ ≠ ![1, 1, 1] →
      σ ≠ ![0, 1, 2] → σ ≠ ![1, 0, 2] →
      grading.blockTensor σ = 0) :
    PiTensorProduct.map (outerExtractionMap grading family)
        (T.kronPow (2 * N)).t =
      (TensorObj.bigAdd (starObj grading family)).t ∧
    outerExtractionMap grading family 2 =
      ∑ a : Fin A,
        (gradedBigAddSlot A (starObj grading family) a 2).comp
          (gradedAddressProj grading (2 * N)
            (componentAddress family a (firstFiberIndex family)) 2) := by
  exact outerExtraction_exact_internal grading family hSupport
