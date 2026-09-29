-- Prove2me | solution 1 for mme_stothers_phi116_outer_hashing_from_address_cyclic_values
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-07T03:04:49.914804+00:00
-- url     : https://prove2.me/submissions/3d521b3b-eff8-49fb-b0ad-79ae839a94f7

import Mathlib
import Theorems.Thm_mme_CW_q6_type2_cyclic_affine_hash_AP
import Theorems.Thm_mme_CW_q6_type2_cyclic_edge_common_label_state_card
import Theorems.Thm_mme_CW_q6_type2_cyclic_pair_common_label_state_card_le
import Theorems.Thm_mme_CW_q6_type2_cyclic_mode_fiber_degree_of_complete_finset
import Theorems.Thm_mme_CW_q6_type2_cyclic_supported_mix_closure
import Theorems.Thm_mme_type2_fractional_retention_of_relative_mode_degree
import Theorems.Thm_mme_stothers_phi116_exact_address_component_factorization
import Theorems.Thm_mme_stothers_phi116_four_edge_support
import Theorems.Thm_mme_cyclic_grading_address_block_iso
import Theorems.Thm_mme_cyclic_triple_grading_nonzero_factors
import Theorems.Thm_mme_induced_graded_address_blocks_restrict
import Theorems.Thm_mme_bigAdd_mono_restrict
import Theorems.Thm_mme_dwz_multinomial_entropy_polynomial_lower
import Theorems.Thm_mme_CW_q6_primary_capacity_factorial_identity
import Theorems.Thm_mme_CW_q6_exact_coupled_address_regularity
import Theorems.Thm_mme_prime_behrend_dominates_bounded_collision_degree
import Theorems.Thm_mme_stothers_phi233_lower_half_cast_label_package
import Theorems.Thm_mme_stothers_phi116_profile_source_cyclic_value_below
import Theorems.Thm_mme_HasTauValueAtLeast_bigAdd_uniform_strict
import Theorems.Thm_mme_HasTauValueAtLeast_mono_restrict
import Theorems.Thm_mme_HasTauValueAtLeast_kronPow_root
universe u


open MME BigOperators
open MME.StothersFourth.Phi116
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 10000
set_option linter.style.haveILetI false

noncomputable local instance phi116AddressFintype (N alpha beta : ℕ) :
    Fintype (CWQ6ExactCoupledAddress N alpha beta) := by
  classical
  unfold CWQ6ExactCoupledAddress CWQ6CoupledAddress
  infer_instance

noncomputable local instance phi116EdgeFintype (N alpha beta : ℕ) :
    Fintype (CWQ6Type2CyclicEdge N alpha beta) := by
  unfold CWQ6Type2CyclicEdge
  infer_instance

theorem phi116_hash_agrees_on_mode
    (p N alpha beta : ℕ)
    (q : (Fin 3 → Fin (2*N) → ZMod p) × ZMod p)
    (i : Fin 3) (e f : CWQ6Type2CyclicEdge N alpha beta)
    (h : cwQ6Type2CyclicModeWord e i = cwQ6Type2CyclicModeWord f i) :
    cwQ6Type2CyclicAffineHash p N alpha beta q i e =
      cwQ6Type2CyclicAffineHash p N alpha beta q i f := by
  have h1 := congrArg Prod.fst h
  have h2 := congrArg (fun v ↦ v.2.1) h
  have h3 := congrArg (fun v ↦ v.2.2) h
  fin_cases i <;>
    simp only [cwQ6Type2CyclicModeWord] at h1 h2 h3 <;>
    simp only [cwQ6Type2CyclicAffineHash, h1, h2, h3]

theorem phi116_finite_hash_selection
    (N alpha beta p : ℕ) (hN : 0 < N) (hsum : alpha + beta = N)
    [Fact p.Prime] (hp : 7 ≤ p) (S : Finset (ZMod p))
    (hfree : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x+y=2*z → x=z ∧ z=y)
    (hlarge : 6 * ((Nat.choose N beta ^ 4 * Nat.choose (2*beta) beta : ℕ) : ℝ) ≤ S.card) :
    ∃ kept : Finset (CWQ6Type2CyclicEdge N alpha beta),
      CWQ6Type2CyclicInducedModeDisjoint kept ∧
      (Fintype.card (CWQ6Type2CyclicEdge N alpha beta) : ℝ) *
        ((S.card : ℝ) / (2 * (p : ℝ)^2)) ≤ kept.card := by
  classical
  let I := (Fin 3 × Fin (2*N)) ⊕ Unit
  let State := (I → ZMod p) × ZMod p
  let weights := fun w : I → ZMod p ↦ fun r j ↦ w (Sum.inl (r,j))
  let H := fun q : State ↦ cwQ6Type2CyclicAffineHash p N alpha beta
    (weights q.1, (6 : ZMod p)⁻¹ * q.2)
  let retain := fun (q : State) (e : CWQ6Type2CyclicEdge N alpha beta) ↦
    ∃ s ∈ S, ∀ i : Fin 3, H q i e = s
  let all : Finset (CWQ6Type2CyclicEdge N alpha beta) := Finset.univ
  let D := Nat.choose N beta ^ 4 * Nat.choose (2*beta) beta
  let ell : ℝ := (S.card : ℝ) / (2 * (p : ℝ)^2)
  have hp0 : 0 < p := by omega
  haveI : NeZero p := ⟨by omega⟩
  have hstate : Fintype.card State = p^2 * p^(6*N) := by
    simp only [State, I, Fintype.card_prod, Fintype.card_fun, Fintype.card_sum,
      Fintype.card_fin, Fintype.card_unit, ZMod.card]
    rw [← pow_succ, ← pow_add]
    congr 1
    omega
  have hdegree (i : Fin 3) (a : CWQ6Type2CyclicEdge N alpha beta) (_ : a ∈ all) :
      (all.filter (fun b ↦ cwQ6Type2CyclicModeWord b i = cwQ6Type2CyclicModeWord a i)).card ≤ D := by
    have hh := mme_CW_q6_type2_cyclic_mode_fiber_degree_of_complete_finset
      N alpha beta hsum Finset.univ (fun _ ↦ Finset.mem_univ _) a i
    have hall :
        (Finset.univ ×ˢ (Finset.univ ×ˢ Finset.univ) :
          Finset (CWQ6Type2CyclicEdge N alpha beta)) = all := by
      ext b
      constructor
      · intro _
        exact Finset.mem_univ b
      · intro _
        exact Finset.mem_product.mpr
          ⟨Finset.mem_univ _, Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩⟩
    rw [hall] at hh
    dsimp only [D]
    omega
  have hedge (a : CWQ6Type2CyclicEdge N alpha beta) (_ : a ∈ all) :
      (Finset.univ.filter (fun q : State ↦ retain q a)).card = S.card * p^(6*N) :=
    mme_CW_q6_type2_cyclic_edge_common_label_state_card hp hN a S
  have hpair (ab : CWQ6Type2CyclicEdge N alpha beta × CWQ6Type2CyclicEdge N alpha beta)
      (hab : ab ∈ ((all ×ˢ all).filter (fun ab ↦ ab.1 ≠ ab.2 ∧
        ∃ i : Fin 3, cwQ6Type2CyclicModeWord ab.1 i = cwQ6Type2CyclicModeWord ab.2 i))) :
      (Finset.univ.filter (fun q : State ↦ retain q ab.1 ∧ retain q ab.2)).card ≤ p^(6*N) := by
    obtain ⟨_, hne, i, hi⟩ := Finset.mem_filter.mp hab
    exact mme_CW_q6_type2_cyclic_pair_common_label_state_card_le hp ab.1 ab.2 S hne i hi
  have hclosure (q : State)
      (x : CWQ6Type2CyclicEdge N alpha beta) (hx : x ∈ all.filter (retain q))
      (y : CWQ6Type2CyclicEdge N alpha beta) (hy : y ∈ all.filter (retain q))
      (z : CWQ6Type2CyclicEdge N alpha beta) (hz : z ∈ all.filter (retain q))
      (hs : CWQ6Type2CyclicCoordinatewiseSupported x y z) :
      ∃ e ∈ all.filter (retain q), cwQ6Type2CyclicModeWord e 0 = cwQ6Type2CyclicModeWord x 0 ∧
        cwQ6Type2CyclicModeWord e 1 = cwQ6Type2CyclicModeWord y 1 ∧
        cwQ6Type2CyclicModeWord e 2 = cwQ6Type2CyclicModeWord z 2 := by
    obtain ⟨sx, hsx, hx'⟩ := (Finset.mem_filter.mp hx).2
    obtain ⟨sy, hsy, hy'⟩ := (Finset.mem_filter.mp hy).2
    obtain ⟨sz, hsz, hz'⟩ := (Finset.mem_filter.mp hz).2
    have hap := mme_CW_q6_type2_cyclic_affine_hash_AP (weights q.1, (6 : ZMod p)⁻¹*q.2) x y z hs
    change H q 0 x + H q 1 y = 2 * H q 2 z at hap
    rw [hx', hy', hz'] at hap
    obtain ⟨hxs, hsy'⟩ := hfree sx hsx sy hsy sz hsz hap
    obtain ⟨e, he0, he1, he2⟩ := mme_CW_q6_type2_cyclic_supported_mix_closure x y z hs
    refine ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, he0, he1, he2⟩
    refine ⟨sz, hsz, ?_⟩
    intro i
    fin_cases i
    · exact (phi116_hash_agrees_on_mode _ _ _ _ _ _ _ _ he0).trans ((hx' 0).trans hxs)
    · exact (phi116_hash_agrees_on_mode _ _ _ _ _ _ _ _ he1).trans ((hy' 1).trans hsy'.symm)
    · exact (phi116_hash_agrees_on_mode _ _ _ _ _ _ _ _ he2).trans (hz' 2)
  have hmargin : ((p^2 : ℕ) : ℝ)*ell + 3*(D : ℝ)*(1 : ℝ) ≤ S.card := by
    dsimp [ell, D]
    push_cast
    have hp' : (p : ℝ) ≠ 0 := by positivity
    have heq : (p : ℝ)^2 * ((S.card : ℝ) / (2 * (p : ℝ)^2)) = (S.card : ℝ)/2 := by field_simp
    rw [heq]
    have hlarge' := hlarge
    push_cast at hlarge'
    nlinarith only [hlarge']
  obtain ⟨q, kept, _, hmode, hdiag, hcard⟩ :=
    mme_type2_fractional_retention_of_relative_mode_degree
      (fun i e ↦ cwQ6Type2CyclicModeWord e i) CWQ6Type2CyclicCoordinatewiseSupported
      all all retain (p^2) S.card (p^(6*N)) D 1 (all.card : ℝ) (D : ℝ) ell
      (by positivity) hstate (by simp) hdegree (by simp) hedge hpair
      (by rfl) hclosure (by simpa only [Nat.cast_one] using hmargin)
  exact ⟨kept, ⟨hmode,hdiag⟩, by simpa only [all, Finset.card_univ, ell] using hcard⟩

theorem kron_restrict
    {K : Type u} [Field K] {d : ℕ} (hd : 1 < d)
    {X X' Y Y' : TensorObj K d}
    (hX : TensorObj.Restrict X X')
    (hY : TensorObj.Restrict Y Y') :
    TensorObj.Restrict (TensorObj.kron X Y) (TensorObj.kron X' Y') := by
  let P := TensorQ.tensorStrassen K d hd
  have hx : TensorQ.le (TensorQ.toQ X) (TensorQ.toQ X') :=
    (TensorQ.le_toQ X X').2 hX
  have hy : TensorQ.le (TensorQ.toQ Y) (TensorQ.toQ Y') :=
    (TensorQ.le_toQ Y Y').2 hY
  have hleft := P.mul_right _ _ hx (TensorQ.toQ Y)
  have hright := P.mul_right _ _ hy (TensorQ.toQ X')
  apply (TensorQ.le_toQ _ _).1
  rw [TensorQ.toQ_kron, TensorQ.toQ_kron]
  exact P.le_trans _ _ _ hleft (by simpa only [mul_comm] using hright)

def phi116_cyclic_address {N alpha beta : ℕ}
    (e : CWQ6Type2CyclicEdge N alpha beta) : Fin 3 → Fin (2*N) → Fin 27 :=
  fun i j ↦ mmeCyclicTripleGrade (fun s ↦ e.1.1 s j)
    (fun s ↦ e.2.1.1 s j) (fun s ↦ e.2.2.1 s j) i

theorem phi116_cyclic_product_restrict
    {K : Type u} [Field K] {N alpha beta : ℕ} (hsum : alpha+beta=N)
    (e : CWQ6Type2CyclicEdge N alpha beta) :
    TensorObj.Restrict
      (cyclicSymmetrization (TensorObj.kronFin 4 (fun r ↦
        (phi116ComponentObj K r).kronPow (phi116ComponentMultiplicity alpha beta r))))
      (gradedAddressBlock (mmeCyclicTripleGrading (cwPhi116ThreeGrading K))
        (phi116_cyclic_address e)) := by
  have hA := mme_stothers_phi116_exact_address_component_factorization (K := K) hsum e.1
  have hB := mme_stothers_phi116_exact_address_component_factorization (K := K) hsum e.2.1
  have hC := mme_stothers_phi116_exact_address_component_factorization (K := K) hsum e.2.2
  have hh := kron_restrict (K := K) (by omega) hA
    (kron_restrict (K := K) (by omega)
      (TensorObj.permObj_restrict cyclicPerm hB)
      (TensorObj.permObj_restrict (cyclicPerm.trans cyclicPerm) hC))
  rw [cyclicSymmetrization_eq_public_perm]
  exact hh.trans (mme_cyclic_grading_address_block_iso (cwPhi116ThreeGrading K)
    e.1.1 e.2.1.1 e.2.2.1).1

theorem phi116_supported_of_nonzero
    {K : Type u} [Field K] (rho : Fin 3 → Fin 3)
    (h : (cwPhi116ThreeGrading K).blockTensor rho ≠ 0) :
    (rho 0=0 ∧ rho 1=0 ∧ rho 2=0) ∨ (rho 0=1 ∧ rho 1=1 ∧ rho 2=1) ∨
    (rho 0=0 ∧ rho 1=1 ∧ rho 2=2) ∨ (rho 0=1 ∧ rho 1=0 ∧ rho 2=2) := by
  have hr : rho = ![0,0,0] ∨ rho = ![1,1,1] ∨ rho = ![0,1,2] ∨ rho = ![1,0,2] := by
    by_contra! hn
    exact h (mme_stothers_phi116_four_edge_support (K := K) rho hn.1 hn.2.1 hn.2.2.1 hn.2.2.2)
  rcases hr with rfl | rfl | rfl | rfl <;> decide

theorem phi116_cyclic_mixed_supported
    {K : Type u} [Field K] {N alpha beta : ℕ}
    (x y z : CWQ6Type2CyclicEdge N alpha beta)
    (hnz : ∀ j, (mmeCyclicTripleGrading (cwPhi116ThreeGrading K)).blockTensor
      (fun i ↦ phi116_cyclic_address (![x,y,z] i) i j) ≠ 0) :
    CWQ6Type2CyclicCoordinatewiseSupported x y z := by
  have hh (j : Fin (2*N)) :
      (fun i ↦ phi116_cyclic_address (![x,y,z] i) i j) =
      mmeCyclicTripleGrade
        (fun s ↦ cwQ6CoupledMixedAddress x.1.1 y.1.1 z.1.1 s j)
        (fun s ↦ cwQ6CoupledMixedAddress y.2.1.1 z.2.1.1 x.2.1.1 s j)
        (fun s ↦ cwQ6CoupledMixedAddress z.2.2.1 x.2.2.1 y.2.2.1 s j) := by
    funext i
    fin_cases i <;> rfl
  have hparts (j : Fin (2*N)) := mme_cyclic_triple_grading_nonzero_factors
    (cwPhi116ThreeGrading K) _ _ _ (by rw [← hh j]; exact hnz j)
  refine ⟨?_, ?_, ?_⟩
  · intro j; exact phi116_supported_of_nonzero _ (hparts j).1
  · intro j; exact phi116_supported_of_nonzero _ (hparts j).2.1
  · intro j; exact phi116_supported_of_nonzero _ (hparts j).2.2

theorem phi116_induced_profile_restrict
    {K : Type u} [Field K] {N alpha beta : ℕ} (hsum : alpha+beta=N)
    (kept : Finset (CWQ6Type2CyclicEdge N alpha beta))
    (hdiag : ∀ x y z : kept, CWQ6Type2CyclicCoordinatewiseSupported x.1 y.1 z.1 → x=y ∧ y=z) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun _ : Fin kept.card ↦
        cyclicSymmetrization (TensorObj.kronFin 4 (fun r ↦
          (phi116ComponentObj K r).kronPow (phi116ComponentMultiplicity alpha beta r)))))
      ((cyclicSymmetrization (MME.StothersFourth.cwFourthConstituent K 6 1 1 6)).kronPow (2*N)) := by
  classical
  let A := fun j : Fin kept.card ↦ phi116_cyclic_address (kept.equivFin.symm j).1
  have hind (js : Fin 3 → Fin kept.card)
      (hnz : ∀ r, (mmeCyclicTripleGrading (cwPhi116ThreeGrading K)).blockTensor
        (fun i ↦ A (js i) i r) ≠ 0) : ∃ j, js = fun _ ↦ j := by
    let es := fun i ↦ kept.equivFin.symm (js i)
    have hs := phi116_cyclic_mixed_supported (K := K) (es 0).1 (es 1).1 (es 2).1 (by
      intro j
      have he : (![(es 0).1, (es 1).1, (es 2).1] : Fin 3 → CWQ6Type2CyclicEdge N alpha beta) =
          fun i ↦ (es i).1 := by funext i; fin_cases i <;> rfl
      rw [he]
      exact hnz j)
    obtain ⟨h01,h12⟩ := hdiag (es 0) (es 1) (es 2) hs
    have hj01 : js 0 = js 1 := kept.equivFin.symm.injective h01
    have hj12 : js 1 = js 2 := kept.equivFin.symm.injective h12
    refine ⟨js 0, ?_⟩
    funext i
    fin_cases i <;> simp_all
  have hh := mme_induced_graded_address_blocks_restrict
    (mmeCyclicTripleGrading (cwPhi116ThreeGrading K)) A hind
  refine TensorObj.Restrict.trans (mme_bigAdd_mono_restrict ?_) hh
  intro j
  exact phi116_cyclic_product_restrict hsum (kept.equivFin.symm j).1

open MME Real BigOperators Filter
set_option autoImplicit false
set_option maxHeartbeats 200000

theorem phi116_real_multinomial_lower
    {R : Type*} [Fintype R] (w : R → ℕ) (n : ℕ)
    (hn : 0 < n) (hsum : ∑ i, w i = n) :
    Real.exp ((n : ℝ) * ∑ i, Real.negMulLog ((w i : ℝ) / n)) ≤
      (6 * ((n + 1 : ℕ) : ℝ)) ^ Fintype.card R *
        ((n.factorial : ℝ) / ∏ i, ((w i).factorial : ℝ)) := by
  have hw : 0 < ∑ i, w i := by omega
  have h := mme_dwz_multinomial_entropy_polynomial_lower w 1 (by omega) hw
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  simp only [hsum, mul_one, mme_modern_entropyBits] at h
  have hcancel (x : ℝ) : (n : ℝ) * Real.log 2 * (x / Real.log 2) = n * x := by field_simp
  rw [hcancel] at h
  simp only [Nat.multinomial, hsum, Nat.cast_one, one_mul] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  simpa only [Nat.cast_prod] using (Nat.cast_div_le (α := ℝ)
    (m := n.factorial) (n := ∏ i, (w i).factorial))

theorem phi116_degree_bounds (N alpha beta : ℕ) (hsum : alpha+beta=N) :
    1 ≤ Nat.choose N beta ^ 4 * Nat.choose (2*beta) beta ∧
    Nat.choose N beta ^ 4 * Nat.choose (2*beta) beta ≤ 5^(6*N) := by
  have hbN : beta ≤ N := by omega
  have h1 := Nat.choose_pos hbN
  have h2 := Nat.choose_pos (show beta ≤ 2*beta by omega)
  refine ⟨Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Nat.mul_pos (Nat.pow_pos h1) h2)), ?_⟩
  calc
    Nat.choose N beta ^ 4 * Nat.choose (2*beta) beta ≤
        (2^N)^4 * 2^(2*beta) := Nat.mul_le_mul
      (Nat.pow_le_pow_left (Nat.choose_le_two_pow N beta) 4) (Nat.choose_le_two_pow (2*beta) beta)
    _ = 2^(4*N+2*beta) := by rw [← pow_mul, ← pow_add]; congr 1; omega
    _ ≤ 2^(6*N) := Nat.pow_le_pow_right (by omega) (by omega)
    _ ≤ 5^(6*N) := Nat.pow_le_pow_left (by omega) _

theorem phi116_prime_parameters (N alpha beta : ℕ) (hsum : alpha+beta=N) :
    ∃ p : ℕ, Nat.Prime p ∧ 7 ≤ p ∧ ∃ S : Finset (ZMod p),
      (∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x+y=2*z → x=z ∧ z=y) ∧
      6 * ((Nat.choose N beta ^ 4 * Nat.choose (2*beta) beta : ℕ) : ℝ) ≤ S.card ∧
      (p : ℝ) ≤ ((Nat.choose N beta ^ 4 * Nat.choose (2*beta) beta : ℕ) : ℝ) *
        Real.exp (2000 * Real.sqrt ((6*N+1 : ℕ) : ℝ)) := by
  classical
  let D := Nat.choose N beta ^ 4 * Nat.choose (2*beta) beta
  obtain ⟨hD1,hD5⟩ := phi116_degree_bounds N alpha beta hsum
  obtain ⟨p,hp,hp5,S,hSr,hSf,hSbig,hpbound⟩ :=
    mme_prime_behrend_dominates_bounded_collision_degree (6*N) D hD1 hD5
  have hcard := Finset.card_le_card hSr
  rw [Finset.card_range] at hcard
  have hScard : 6*D ≤ S.card := by exact_mod_cast hSbig
  have hp7 : 7 ≤ p := by omega
  obtain ⟨hcastcard,hcastfree⟩ := mme_stothers_phi233_lower_half_cast_label_package p S hSr hSf
  exact ⟨p,hp,hp7,S.image (fun s : ℕ ↦ (s : ZMod p)),hcastfree,
    by simpa only [hcastcard] using hSbig, hpbound⟩

noncomputable def phi116_entropy (a b : ℝ) : ℝ :=
  2 * Real.log 2 + 2 * Real.negMulLog (a/2) + Real.negMulLog b

theorem phi116_factorial_entropy
    (N alpha beta : ℕ) (hN : 0 < N) (hsum : alpha+beta=N) :
    Real.exp ((2*N : ℝ) * phi116_entropy (alpha/N) (beta/N)) ≤
      (6*((2*N+1 : ℕ) : ℝ))^9 *
        (((2*N).factorial : ℝ)^3 /
          ((alpha.factorial : ℝ)^2 * ((2*beta).factorial : ℝ) * (N.factorial : ℝ)^4)) := by
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  have hx := phi116_real_multinomial_lower (![N,N,0] : Fin 3 → ℕ) (2*N) (by omega) (by simp [Fin.sum_univ_succ]; omega)
  have hz := phi116_real_multinomial_lower (![alpha,alpha,2*beta] : Fin 3 → ℕ) (2*N) (by omega) (by simp [Fin.sum_univ_succ]; omega)
  norm_num [Fin.sum_univ_succ, Fin.prod_univ_succ] at hx hz
  have hhalf : (N : ℝ)/(2*N)=1/2 := by field_simp
  rw [hhalf] at hx
  have henthalf : Real.negMulLog (1/2) = Real.log 2 / 2 := by
    norm_num [Real.negMulLog, Real.log_div]
    ring
  rw [henthalf] at hx
  have heqx : (2*N : ℝ)*(Real.log 2 / 2 + Real.log 2 / 2) = (2*N : ℝ)*Real.log 2 := by ring
  rw [heqx] at hx
  have h1 : (alpha : ℝ)/(2*N)=(alpha/N)/2 := by ring
  have h2 : (2*beta : ℝ)/(2*N)=beta/N := by ring
  rw [h1,h2] at hz
  have hh := mul_le_mul (mul_self_le_mul_self (Real.exp_pos _).le hx) hz
    (Real.exp_pos _).le (by positivity)
  have heq :
      Real.exp ((2*N : ℝ)*Real.log 2) * Real.exp ((2*N : ℝ)*Real.log 2) *
      Real.exp ((2*N : ℝ)*(Real.negMulLog ((alpha/N)/2)+
        (Real.negMulLog ((alpha/N)/2)+Real.negMulLog (beta/N)))) =
      Real.exp ((2*N : ℝ)*phi116_entropy (alpha/N) (beta/N)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    unfold phi116_entropy
    ring
  rw [heq] at hh
  convert hh using 1 <;> push_cast <;> try ring
  rfl

theorem phi116_exact_card (N alpha beta : ℕ) (hsum : alpha+beta=N) :
    Nat.card (CWQ6ExactCoupledAddress N alpha beta) =
      (Nat.choose (2*N) alpha * Nat.choose (2*N-alpha) alpha) * Nat.choose (2*beta) beta := by
  classical
  let e : CWQ6ExactCoupledAddress N alpha beta ≃
      ↥(cwQ6ExactAddresses N alpha beta) :=
    { toFun := fun a => ⟨a.1, by
        simp only [cwQ6ExactAddresses, Finset.mem_filter, Finset.mem_univ, true_and]
        exact a.2⟩
      invFun := fun a => ⟨a.1, by
        have ha := a.2
        simp only [cwQ6ExactAddresses, Finset.mem_filter, Finset.mem_univ, true_and] at ha
        exact ha⟩
      left_inv := by
        intro a
        apply Subtype.ext
        rfl
      right_inv := by
        intro a
        apply Subtype.ext
        rfl }
  calc
    Nat.card (CWQ6ExactCoupledAddress N alpha beta) =
        Fintype.card (CWQ6ExactCoupledAddress N alpha beta) := Nat.card_eq_fintype_card
    _ = Fintype.card ↥(cwQ6ExactAddresses N alpha beta) := Fintype.card_congr e
    _ = (cwQ6ExactAddresses N alpha beta).card := Fintype.card_coe _
    _ = _ := (mme_CW_q6_exact_coupled_address_regularity N alpha beta hsum).total_card

theorem phi116_capacity_entropy
    (N alpha beta : ℕ) (hN : 0 < N) (hsum : alpha+beta=N) :
    Real.exp ((2*N : ℝ)*phi116_entropy (alpha/N) (beta/N)) ≤
      (6*((2*N+1 : ℕ) : ℝ))^9 *
        ((Nat.card (CWQ6ExactCoupledAddress N alpha beta) : ℝ)^3 /
          ((Nat.choose N beta ^ 4 * Nat.choose (2*beta) beta : ℕ) : ℝ)) := by
  have hx : 0 < (Nat.choose N beta : ℝ) := by exact_mod_cast Nat.choose_pos (show beta ≤ N by omega)
  have hb : 0 < (Nat.choose (2*beta) beta : ℝ) := by exact_mod_cast Nat.choose_pos (show beta ≤ 2*beta by omega)
  have hid := mme_CW_q6_primary_capacity_factorial_identity N alpha beta hsum
  dsimp only at hid
  push_cast at hid
  have hcap :
      ((Nat.card (CWQ6ExactCoupledAddress N alpha beta) : ℝ)^3 /
          ((Nat.choose N beta ^ 4 * Nat.choose (2*beta) beta : ℕ) : ℝ)) =
      ((2*N).factorial : ℝ)^3 /
        ((alpha.factorial : ℝ)^2 * ((2*beta).factorial : ℝ) * (N.factorial : ℝ)^4) := by
    rw [phi116_exact_card N alpha beta hsum]
    push_cast
    have hh := congrArg (fun x : ℝ ↦ 16*x) hid
    field_simp at hh ⊢
    nlinarith only [hh]
  rw [hcap]
  exact phi116_factorial_entropy N alpha beta hN hsum

theorem phi116_entropy_rate_identity
    (a X Y : ℝ) (ha : 0 < a) (ha1 : a < 1) (hX : 0 < X) (hY : 0 < Y) :
    phi116_entropy a (1-a) + a*Real.log X + (1-a)*Real.log Y =
      Real.log (4 * ((2*X/a)^a * (Y/(1-a))^(1-a))) := by
  have hb : 0 < 1-a := by linarith
  have hxa : 0 < 2*X/a := by positivity
  have hyb : 0 < Y/(1-a) := by positivity
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_rpow hxa, Real.log_rpow hyb,
    Real.log_div (by positivity) ha.ne', Real.log_div hY.ne' hb.ne',
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hX.ne']
  have h4 : Real.log 4=2*Real.log 2 := by
    rw [show (4 : ℝ)=2^2 by norm_num, Real.log_pow]
    norm_num
  rw [h4]
  unfold phi116_entropy
  rw [Real.negMulLog, Real.negMulLog, Real.log_div ha.ne' (by norm_num : (2 : ℝ) ≠ 0)]
  ring

theorem phi116_scaled_log_limit (s : ℝ) (hs : 0 < s) :
    Tendsto (fun n : ℕ ↦ Real.log (s * n + 1) / (2 * n)) atTop (nhds 0) := by
  have ht : Tendsto (fun n : ℕ ↦ s * (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop.const_mul_atTop hs)
  have hl := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp ht
  have hr : Tendsto (fun n : ℕ ↦ (s * n + 1) / (2 * n)) atTop (nhds (s / 2)) := by
    have hi : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have hh := ((tendsto_const_nhds (x := s)).add hi).div_const (2 : ℝ)
    convert hh.congr' ?_ using 1
    · simp
    · filter_upwards [eventually_gt_atTop 0] with n hn
      have hn' : (n : ℝ) ≠ 0 := by positivity
      field_simp
  have hh := hl.mul hr
  convert hh.congr' ?_ using 1
  · simp
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hpos : 0 < s * (n : ℝ) + 1 := by positivity
    simp only [Function.comp_apply, pow_one, one_mul, add_zero]
    field_simp

theorem phi116_scaled_sqrt_limit (s : ℝ) (hs : 0 < s) :
    Tendsto (fun n : ℕ ↦ Real.sqrt (s * n + 1) / (2 * n)) atTop (nhds 0) := by
  have ht : Tendsto (fun n : ℕ ↦ s * (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop.const_mul_atTop hs)
  have hi := tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp ht)
  have hr : Tendsto (fun n : ℕ ↦ (s * n + 1) / (2 * n)) atTop (nhds (s / 2)) := by
    have hin : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have hh := ((tendsto_const_nhds (x := s)).add hin).div_const (2 : ℝ)
    convert hh.congr' ?_ using 1
    · simp
    · filter_upwards [eventually_gt_atTop 0] with n hn
      have hn' : (n : ℝ) ≠ 0 := by positivity
      field_simp
  have hh := hi.mul hr
  convert hh.congr' ?_ using 1
  · simp
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hpos : 0 < s * (n : ℝ) + 1 := by positivity
    have hsqrt : Real.sqrt (s * n + 1) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
    simp only [Function.comp_apply]
    field_simp
    nlinarith [Real.sq_sqrt hpos.le]


theorem phi116_penalty_limit :
    Tendsto (fun n : ℕ ↦ (9*Real.log (6*((2*n+1 : ℕ) : ℝ)) +
      4000*Real.sqrt ((6*n+1 : ℕ) : ℝ) + Real.log 16) / (2*n)) atTop (nhds 0) := by
  have hl := phi116_scaled_log_limit 2 (by norm_num)
  have hs := phi116_scaled_sqrt_limit 6 (by norm_num)
  have hi : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hh := ((((hi.const_mul (Real.log 6)).div_const 2).add hl).const_mul 9 |>.add
    (hs.const_mul 4000)).add ((hi.const_mul (Real.log 16)).div_const 2)
  convert hh.congr' ?_ using 1
  · simp
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hp : (2*(n : ℝ)+1) ≠ 0 := by positivity
    push_cast
    rw [Real.log_mul (by norm_num : (6 : ℝ) ≠ 0) hp]
    ring

theorem phi116_profile_surplus
    (L R a V : ℝ) (hL : 0<L) (hR : 0<R) (ha : 0<a) (ha1 : a<1) (hV : 0<V)
    (hVlt : V < 4*((2*L/a)^a * (R/(1-a))^(1-a))) :
    ∃ N alpha beta : ℕ, 0<N ∧ alpha+beta=N ∧
      ∃ X Y : ℝ, 0<X ∧ X<L ∧ 0<Y ∧ Y<R ∧
        V^(2*N) * ((Nat.choose N beta ^ 4 * Nat.choose (2*beta) beta : ℕ) : ℝ) *
          Real.exp (4000*Real.sqrt ((6*N+1 : ℕ) : ℝ)) * 16 <
        (Nat.card (CWQ6ExactCoupledAddress N alpha beta) : ℝ)^3 *
          (X^(2*alpha)*Y^(2*beta)) := by
  let A := fun n : ℕ ↦ Nat.floor (a*(n : ℝ))
  let B := fun n : ℕ ↦ n-A n
  have hAn (n : ℕ) : A n ≤ n := by
    apply Nat.floor_le_of_le
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hsum (n : ℕ) : A n+B n=n := Nat.add_sub_of_le (hAn n)
  have hA : Tendsto (fun n : ℕ ↦ (A n : ℝ)/(n : ℝ)) atTop (nhds a) :=
    (tendsto_nat_floor_mul_div_atTop ha.le).comp tendsto_natCast_atTop_atTop
  have hB : Tendsto (fun n : ℕ ↦ (B n : ℝ)/(n : ℝ)) atTop (nhds (1-a)) := by
    have hh := (tendsto_const_nhds (x := (1 : ℝ))).sub hA
    apply hh.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    dsimp [B]
    rw [Nat.cast_sub (hAn n)]
    field_simp
  let shrink := fun n : ℕ ↦ 1-((n : ℝ)+2)⁻¹
  let X := fun n ↦ L*shrink n
  let Y := fun n ↦ R*shrink n
  have hshrink (n : ℕ) : 0<shrink n ∧ shrink n<1 := by
    have hd : 1 < (n : ℝ)+2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hi0 := inv_pos.mpr (lt_trans (by norm_num : (0 : ℝ)<1) hd)
    have hi1 := (inv_lt_one₀ (by positivity : 0<(n : ℝ)+2)).mpr hd
    dsimp [shrink]
    constructor <;> linarith
  have hX (n : ℕ) : 0<X n ∧ X n<L := by
    exact ⟨mul_pos hL (hshrink n).1, by simpa only [mul_one] using mul_lt_mul_of_pos_left (hshrink n).2 hL⟩
  have hY (n : ℕ) : 0<Y n ∧ Y n<R := by
    exact ⟨mul_pos hR (hshrink n).1, by simpa only [mul_one] using mul_lt_mul_of_pos_left (hshrink n).2 hR⟩
  have hin : Tendsto (fun n : ℕ ↦ ((n : ℝ)+2)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  have hXlim : Tendsto X atTop (nhds L) := by
    simpa only [X, shrink, sub_zero, mul_one] using ((tendsto_const_nhds (x := (1 : ℝ))).sub hin).const_mul L
  have hYlim : Tendsto Y atTop (nhds R) := by
    simpa only [Y, shrink, sub_zero, mul_one] using ((tendsto_const_nhds (x := (1 : ℝ))).sub hin).const_mul R
  let rate := fun n ↦ phi116_entropy (A n/n) (B n/n) +
    (A n/n)*Real.log (X n) + (B n/n)*Real.log (Y n)
  have hneg {f : ℕ → ℝ} {x : ℝ} (h : Tendsto f atTop (nhds x)) :
      Tendsto (fun n ↦ Real.negMulLog (f n)) atTop (nhds (Real.negMulLog x)) :=
    Real.continuous_negMulLog.continuousAt.tendsto.comp h
  have hent : Tendsto (fun n ↦ phi116_entropy (A n/n) (B n/n)) atTop (nhds (phi116_entropy a (1-a))) :=
    (tendsto_const_nhds.add ((hneg (hA.div_const 2)).const_mul 2)).add (hneg hB)
  have hrate := (hent.add (hA.mul (hXlim.log hL.ne'))).add (hB.mul (hYlim.log hR.ne'))
  rw [phi116_entropy_rate_identity a L R ha ha1 hL hR] at hrate
  have hlim := hrate.sub phi116_penalty_limit
  have hlog := Real.log_lt_log hV hVlt
  have hevent := hlim.eventually (eventually_gt_nhds (by simpa only [sub_zero] using hlog))
  obtain ⟨N, hN, hgap⟩ := ((eventually_gt_atTop 0).and hevent).exists
  let alpha := A N
  let beta := B N
  let P : ℝ := 6*((2*N+1 : ℕ) : ℝ)
  let Q : ℝ := ((6*N+1 : ℕ) : ℝ)
  let D : ℝ := ((Nat.choose N beta ^ 4 * Nat.choose (2*beta) beta : ℕ) : ℝ)
  let T : ℝ := (Nat.card (CWQ6ExactCoupledAddress N alpha beta) : ℝ)^3
  have hD : 0<D := by
    have hh := (phi116_degree_bounds N alpha beta (hsum N)).1
    dsimp [D]
    exact_mod_cast (show 0<Nat.choose N beta ^ 4 * Nat.choose (2*beta) beta by omega)
  have hP : 0<P := by dsimp [P]; positivity
  have hXN := (hX N).1
  have hYN := (hY N).1
  have hpow : 0<X N^(2*alpha)*Y N^(2*beta) := by positivity
  have hf := mul_le_mul_of_nonneg_right (phi116_capacity_entropy N alpha beta hN (hsum N)) hpow.le
  have hlogC : Real.log (X N^(2*alpha)*Y N^(2*beta)) =
      (2*N : ℝ)*((alpha/N)*Real.log (X N)+(beta/N)*Real.log (Y N)) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    push_cast
    have hn0 : (N : ℝ) ≠ 0 := by positivity
    field_simp
  have hleft : Real.exp ((2*N : ℝ)*phi116_entropy (alpha/N) (beta/N)) *
      (X N^(2*alpha)*Y N^(2*beta)) = Real.exp ((2*N : ℝ)*rate N) := by
    rw [← Real.exp_log hpow, ← Real.exp_add, hlogC]
    congr 1
    dsimp [rate, alpha, beta]
    ring
  rw [hleft] at hf
  have hngap : (2*N : ℝ)*Real.log V + 9*Real.log P + 4000*Real.sqrt Q + Real.log 16 <
      (2*N : ℝ)*rate N := by
    have hh := mul_lt_mul_of_pos_left hgap (by positivity : (0 : ℝ)<2*N)
    change (2*N : ℝ)*Real.log V < (2*N : ℝ)*(rate N-
      (9*Real.log P+4000*Real.sqrt Q+Real.log 16)/(2*N)) at hh
    have hn0 : (N : ℝ) ≠ 0 := by positivity
    field_simp at hh
    nlinarith only [hh]
  have heq : (2*N : ℝ)*Real.log V + 9*Real.log P + 4000*Real.sqrt Q + Real.log 16 =
      Real.log (V^(2*N)*P^9*Real.exp (4000*Real.sqrt Q)*16) := by
    conv_rhs =>
      rw [Real.log_mul (by positivity) (by norm_num : (16 : ℝ) ≠ 0),
        Real.log_mul (by positivity) (Real.exp_pos _).ne',
        Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_exp]
    push_cast
    ring
  have hh := (Real.exp_lt_exp.mpr hngap).trans_le hf
  rw [heq, Real.exp_log (by positivity)] at hh
  change V^(2*N)*P^9*Real.exp (4000*Real.sqrt Q)*16 < P^9*(T/D)*(X N^(2*alpha)*Y N^(2*beta)) at hh
  have hc : V^(2*N)*Real.exp (4000*Real.sqrt Q)*16 < (T/D)*(X N^(2*alpha)*Y N^(2*beta)) := by
    have hp9 : 0<P^9 := by positivity
    nlinarith only [hh, hp9]
  have hc' := mul_lt_mul_of_pos_right hc hD
  refine ⟨N,alpha,beta,hN,hsum N,X N,Y N,(hX N).1,(hX N).2,(hY N).1,(hY N).2,?_⟩
  change V^(2*N)*D*Real.exp (4000*Real.sqrt Q)*16 < T*(X N^(2*alpha)*Y N^(2*beta))
  field_simp at hc'
  nlinarith only [hc']

open MME BigOperators Filter
open MME.StothersFourth.Phi116
set_option autoImplicit false
set_option maxHeartbeats 200000

theorem phi116_weighted_retention_bound
    (P D F S C M B V : ℝ)
    (hP : 0 < P) (hD : 0 < D) (hF : 0 < F)
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hprime : P ≤ D * F)
    (hlabels : 6 * D ≤ S)
    (hkept : C * (S / (2 * P ^ 2)) ≤ M)
    (hbudget : V * D * F ^ 2 < C * B) :
    V < M * B := by
  have hp2 : 0 < 2 * P ^ 2 := by positivity
  have hcount : C * S ≤ M * (2 * P ^ 2) := by
    apply (div_le_iff₀ hp2).mp
    simpa only [mul_div_assoc] using hkept
  have hleft : 6 * D * C ≤ M * (2 * P ^ 2) := by
    have := mul_le_mul_of_nonneg_left hlabels hC
    nlinarith
  have hsq : P ^ 2 ≤ (D * F) ^ 2 :=
    pow_le_pow_left₀ hP.le hprime 2
  have hright : M * (2 * P ^ 2) ≤ M * (2 * (D * F) ^ 2) := by
    gcongr
  have hboth := hleft.trans hright
  have hmargin : C ≤ M * (D * F ^ 2) := by
    nlinarith [mul_pos hD hF]
  have hweighted := mul_le_mul_of_nonneg_right hmargin hB
  have hpos : 0 < D * F ^ 2 := by positivity
  apply (mul_lt_mul_iff_left₀ hpos).mp
  nlinarith

theorem phi116_value_downward {K : Type u} [Field K]
    (T : TensorObj K 3) (tau B V : ℝ) (h : HasTauValueAtLeast T tau B)
    (hV : 0≤V) (hVB : V≤B) : HasTauValueAtLeast T tau V := by
  refine ⟨hV, ?_⟩
  intro eps heps
  apply (h.2 eps heps).mono
  rintro N ⟨k,a,b,c,hr,hbound⟩
  refine ⟨k,a,b,c,hr,?_⟩
  by_cases heps1 : eps≤1
  · exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hV hVB _) (by linarith)).trans hbound
  · exact (mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hV _) (by linarith)).trans
      (Finset.sum_nonneg (fun _ _ ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _))

theorem solution
    {K : Type u} [Field K] (tau a : Real)
    (htauLower : 2 ≤ 3 * tau) (_htauUpper : 3 * tau ≤ 3)
    (haPos : 0 < a) (haLt : a < 1)
    (_haddress :
      ∀ {N alpha beta : ℕ}, alpha + beta = N →
        ∀ address : CWQ6ExactCoupledAddress N alpha beta,
          ∀ W : Fin 4 → ℝ,
            (∀ r, 0 < W r) →
            (W 0 < MME.StothersFourth.L 6 tau ∧
              W 1 < MME.StothersFourth.L 6 tau) →
            (W 2 < MME.StothersFourth.E 6 tau ^ (2 : ℕ) ∧
              W 3 < MME.StothersFourth.E 6 tau ^ (2 : ℕ)) →
            HasTauValueAtLeast
              (cyclicSymmetrization
                (gradedAddressBlock
                  (MME.StothersFourth.Phi116.cwPhi116ThreeGrading K)
                  address.1)) tau
              (∏ r : Fin 4,
                (W r ^
                  MME.StothersFourth.Phi116.phi116ComponentMultiplicity
                    alpha beta r) / 2)) :
    ∀ V : Real, 0 ≤ V →
      V < 4 *
        (((2 * MME.StothersFourth.L 6 tau) / a) ^ a *
          ((MME.StothersFourth.E 6 tau ^ (2 : ℕ)) / (1 - a)) ^
            (1 - a)) →
      HasTauValueAtLeast
        (cyclicSymmetrization
          (MME.StothersFourth.cwFourthConstituent K 6 1 1 6)) tau V := by
  classical
  intro V hV hVlt
  let L := MME.StothersFourth.L 6 tau
  let R := MME.StothersFourth.E 6 tau ^ (2 : ℕ)
  let Z := 4*((2*L/a)^a*(R/(1-a))^(1-a))
  let U := (V+Z)/2
  have hVU : V<U := by dsimp [U,Z,L,R]; linarith
  have hU : 0<U := lt_of_le_of_lt hV hVU
  have hUZ : U<Z := by dsimp [U,Z,L,R]; linarith
  have hL : 0<L := by unfold L MME.StothersFourth.L; positivity
  have hR : 0<R := by unfold R MME.StothersFourth.E; positivity
  obtain ⟨N,alpha,beta,hN,hsum,X,Y,hX,hXL,hY,hYR,hsurplus⟩ :=
    phi116_profile_surplus L R a U hL hR haPos haLt hU hUZ
  let D : ℝ := ((Nat.choose N beta ^ 4 * Nat.choose (2*beta) beta : ℕ) : ℝ)
  let F := Real.exp (2000*Real.sqrt ((6*N+1 : ℕ) : ℝ))
  let C : ℝ := (Nat.card (CWQ6ExactCoupledAddress N alpha beta) : ℝ)^3
  let B := X^(2*alpha)*Y^(2*beta)/16
  have hD : 0<D := by
    have hh := (phi116_degree_bounds N alpha beta hsum).1
    dsimp [D]
    exact_mod_cast (show 0<Nat.choose N beta ^ 4 * Nat.choose (2*beta) beta by omega)
  have hF : 0<F := Real.exp_pos _
  have hB : 0<B := by dsimp [B]; positivity
  obtain ⟨p,hp,hp7,S,hfree,hlarge,hpbound⟩ := phi116_prime_parameters N alpha beta hsum
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨kept,⟨hmode,hdiag⟩,hcount⟩ := phi116_finite_hash_selection N alpha beta p hN hsum hp7 S hfree hlarge
  have hcard : (Fintype.card (CWQ6Type2CyclicEdge N alpha beta) : ℝ)=C := by
    rw [← Nat.card_eq_fintype_card]
    dsimp [CWQ6Type2CyclicEdge,C]
    rw [Nat.card_prod,Nat.card_prod]
    push_cast
    ring
  rw [hcard] at hcount
  have hFsq : F^2=Real.exp (4000*Real.sqrt ((6*N+1 : ℕ) : ℝ)) := by
    dsimp [F]
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  have hstrict : V^(2*N)*D*F^2<C*B := by
    rw [hFsq]
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hV hVU.le (2*N)) hD.le)
      (Real.exp_pos (4000*Real.sqrt ((6*N+1 : ℕ) : ℝ))).le
    change U^(2*N)*D*Real.exp (4000*Real.sqrt ((6*N+1 : ℕ) : ℝ))*16 < C*(X^(2*alpha)*Y^(2*beta)) at hsurplus
    dsimp [B]
    linarith
  have hVB : V^(2*N)<(kept.card : ℝ)*B :=
    phi116_weighted_retention_bound (p : ℝ) D F S.card C kept.card B (V^(2*N))
      (by exact_mod_cast hp.pos) hD hF (by dsimp [C]; positivity) (by positivity) hB.le
      hpbound hlarge hcount hstrict
  let W : Fin 4 → ℝ := ![X,X,Y,Y]
  have hW : ∀ r, 0<W r := by intro r; fin_cases r <;> simp [W,hX,hY]
  have hBform : (∏ r : Fin 4, W r ^ phi116ComponentMultiplicity alpha beta r / 2)=B := by
    rw [Fin.prod_univ_four]
    change (X^alpha/2)*(X^alpha/2)*(Y^beta/2)*(Y^beta/2)=B
    dsimp [B]
    simp only [pow_mul,pow_two]
    ring
  have hvalue := mme_stothers_phi116_profile_source_cyclic_value_below
    (K := K) tau htauLower alpha beta W hW ⟨hXL,hXL⟩ ⟨hYR,hYR⟩
  rw [hBform] at hvalue
  have hsumvalue := mme_HasTauValueAtLeast_bigAdd_uniform_strict
    (fun _ : Fin kept.card ↦ cyclicSymmetrization (TensorObj.kronFin 4
      (fun r ↦ (phi116ComponentObj K r).kronPow (phi116ComponentMultiplicity alpha beta r))))
    tau B hB.le (fun _ W hW hWB ↦ phi116_value_downward _ tau B W hvalue hW hWB.le)
    (V^(2*N)) (pow_nonneg hV _) hVB
  have hpower := mme_HasTauValueAtLeast_mono_restrict (phi116_induced_profile_restrict (K := K) hsum kept hdiag) hsumvalue
  exact mme_HasTauValueAtLeast_kronPow_root _ tau V (2*N) (by omega) hV hpower
