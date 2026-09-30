-- Prove2me | solution 1 for mme_CW_q6_primary_hash_bucket_collision_budget_averaging
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T09:29:00.650141+00:00
-- url     : https://prove2.me/submissions/2502322d-48f6-42d4-8d06-52a34471e759

import Mathlib.GroupTheory.Perm.DomMulAct
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib
import Definitions.Def_mme_CW_q6_exact_address_incidence
import Mathlib.Tactic.Ring
import Definitions.Def_mme_CW_q6_doubled_hash_arithmetic
import Mathlib.Combinatorics.Additive.AP.Three.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic
import Definitions.Def_mme_CW_q6_primary_hash_bucket











-- Begin complete component: Closure.lean





namespace PruningClosure

-- Accepted source by marwahaha; submission 73e5289c-8709-4cd4-9506-bf54a0560186.



open Equiv MulAction

set_option autoImplicit false

/-- Functions on a finite domain with the same fiber sizes as a fixed
function are counted by the corresponding multinomial coefficient. -/
theorem mme_fintype_fixed_fiber_function_card
    {α ι : Type*} [Fintype α] [Fintype ι]
    [DecidableEq α] [DecidableEq ι] (f : α → ι) :
    Fintype.card
        {g : α → ι // ∀ i,
          Fintype.card {a // g a = i} =
            Fintype.card {a // f a = i}} =
      (Fintype.card α).factorial /
        ∏ i, (Fintype.card {a // f a = i}).factorial := by
  classical
  let G := (Equiv.Perm α)ᵈᵐᵃ
  letI : Fintype G := Fintype.ofEquiv (Equiv.Perm α) DomMulAct.mk
  let P : (α → ι) → Prop := fun g => ∀ i,
    Fintype.card {a // g a = i} = Fintype.card {a // f a = i}
  have horbit : ∀ g : α → ι,
      g ∈ MulAction.orbit G f ↔ P g := by
    intro g
    constructor
    · rw [MulAction.mem_orbit_iff]
      rintro ⟨c, rfl⟩ i
      let e : {a // (c • f) a = i} ≃ {a // f a = i} :=
        Equiv.subtypeEquiv (DomMulAct.mk.symm c) (fun a => by
          change (f (DomMulAct.mk.symm c a) = i) ↔
            f (DomMulAct.mk.symm c a) = i
          rfl)
      exact Fintype.card_congr e
    · intro hg
      let e : ∀ i, {a // g a = i} ≃ {a // f a = i} :=
        fun i => Fintype.equivOfCardEq (hg i)
      let π : Equiv.Perm α := Equiv.ofFiberEquiv e
      rw [MulAction.mem_orbit_iff]
      refine ⟨DomMulAct.mk π, ?_⟩
      funext a
      change f (π a) = g a
      exact Equiv.ofFiberEquiv_map e a
  let orbitEquiv : MulAction.orbit G f ≃ {g : α → ι // P g} :=
    Equiv.subtypeEquiv (Equiv.refl (α → ι)) (fun g => by
      simpa only [Equiv.refl_apply] using horbit g)
  have horbitCard :
      Fintype.card {g : α → ι // P g} *
          Fintype.card (MulAction.stabilizer G f) =
        Fintype.card G := by
    rw [← Fintype.card_congr orbitEquiv]
    exact MulAction.card_orbit_mul_card_stabilizer_eq_card_group G f
  have hstab :
      Fintype.card (MulAction.stabilizer G f) =
        ∏ i, (Fintype.card {a // f a = i}).factorial := by
    let e : MulAction.stabilizer G f ≃
        {g : Equiv.Perm α // f ∘ g = f} :=
      Equiv.subtypeEquiv DomMulAct.mk.symm (fun g => by
        exact DomMulAct.mem_stabilizer_iff)
    rw [Fintype.card_congr e]
    exact DomMulAct.stabilizer_card f
  have hG : Fintype.card G = (Fintype.card α).factorial := by
    exact Fintype.card_congr DomMulAct.mk.symm |>.trans Fintype.card_perm
  change Fintype.card {g : α → ι // P g} = _
  rw [← hstab]
  exact Nat.eq_div_of_mul_eq_left (Fintype.card_ne_zero)
    (by simpa [hG] using horbitCard)

-- Accepted source by marwahaha; submission 5feb9934-3969-4083-8c07-2e0896266f65.


open Equiv

set_option autoImplicit false

/-- A finite histogram whose total is the domain size is realizable, and the
corresponding functions are counted by the multinomial coefficient. -/
theorem mme_fintype_prescribed_fiber_function_card
    {α ι : Type*} [Fintype α] [Fintype ι]
    [DecidableEq α] [DecidableEq ι]
    (k : ι → ℕ) (hsum : ∑ i, k i = Fintype.card α) :
    Fintype.card
        {g : α → ι // ∀ i,
          Fintype.card {a // g a = i} = k i} =
      (Fintype.card α).factorial / ∏ i, (k i).factorial := by
  classical
  let β := Σ i : ι, Fin (k i)
  let e : α ≃ β := Fintype.equivOfCardEq (by
    rw [Fintype.card_sigma]
    simpa using hsum.symm)
  let f : α → ι := fun a => (e a).1
  have hfiber : ∀ i,
      Fintype.card {a // f a = i} = k i := by
    intro i
    let e₁ : {a // f a = i} ≃ {b : β // b.1 = i} :=
      Equiv.subtypeEquiv e (fun a => by rfl)
    calc
      Fintype.card {a // f a = i} =
          Fintype.card {b : β // b.1 = i} := Fintype.card_congr e₁
      _ = Fintype.card (Fin (k i)) :=
        Fintype.card_congr (Equiv.sigmaSubtype i)
      _ = k i := Fintype.card_fin _
  let profileEquiv :
      {g : α → ι // ∀ i, Fintype.card {a // g a = i} = k i} ≃
      {g : α → ι // ∀ i,
        Fintype.card {a // g a = i} =
          Fintype.card {a // f a = i}} :=
    Equiv.subtypeEquiv (Equiv.refl (α → ι)) (fun g => by
      constructor
      · intro hg i
        exact (hg i).trans (hfiber i).symm
      · intro hg i
        exact (hg i).trans (hfiber i))
  rw [Fintype.card_congr profileEquiv,
    mme_fintype_fixed_fiber_function_card f]
  apply congrArg ((Fintype.card α).factorial / ·)
  apply Finset.prod_congr rfl
  intro i hi
  rw [hfiber]

-- Accepted source by marwahaha; submission 951d8ffe-7826-4a56-b34b-78ecab752da2.


open BigOperators

set_option autoImplicit false

theorem mme_fintype_constrained_prescribed_fiber_function_card
    {alpha beta iota : Type*}
    [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta]
    [Fintype iota] [DecidableEq iota]
    (h : alpha → iota) (q : beta → iota) (k : beta → ℕ)
    (hsum : ∀ i,
      (∑ b : {b : beta // q b = i}, k b.1) =
        Fintype.card {a : alpha // h a = i}) :
    Nat.card
        {g : alpha → beta //
          (∀ a, q (g a) = h a) ∧
          ∀ b, Fintype.card {a // g a = b} = k b} =
      ∏ i,
        (Fintype.card {a : alpha // h a = i}).factorial /
          ∏ b : {b : beta // q b = i}, (k b.1).factorial := by
  classical
  let A : iota → Type _ := fun i => {a : alpha // h a = i}
  let B : iota → Type _ := fun i => {b : beta // q b = i}
  let K : ∀ i, B i → ℕ := fun _ b => k b.1

  let sectionEquiv :
      {g : alpha → beta // ∀ a, q (g a) = h a} ≃
        ∀ i, A i → B i := {
    toFun g i a := ⟨g.1 a.1, (g.2 a.1).trans a.2⟩
    invFun G := ⟨fun a => (G (h a) ⟨a, rfl⟩).1, fun a => by
      exact (G (h a) ⟨a, rfl⟩).2⟩
    left_inv g := by
      apply Subtype.ext
      funext a
      rfl
    right_inv G := by
      funext i a
      apply Subtype.ext
      obtain ⟨a, ha⟩ := a
      subst ha
      rfl
  }

  have hfiber (g : {g : alpha → beta // ∀ a, q (g a) = h a})
      (i : iota) (b : B i) :
      Fintype.card {a : A i // sectionEquiv g i a = b} =
        Fintype.card {a : alpha // g.1 a = b.1} := by
    let e : {a : A i // sectionEquiv g i a = b} ≃
        {a : alpha // g.1 a = b.1} := {
      toFun a := ⟨a.1.1, congrArg Subtype.val a.2⟩
      invFun a := by
        have haBase : h a.1 = i := by
          calc
            h a.1 = q (g.1 a.1) := (g.2 a.1).symm
            _ = q b.1 := congrArg q a.2
            _ = i := b.2
        exact ⟨⟨a.1, haBase⟩, Subtype.ext a.2⟩
      left_inv a := by
        apply Subtype.ext
        apply Subtype.ext
        rfl
      right_inv a := by
        apply Subtype.ext
        rfl
    }
    exact Fintype.card_congr e

  let goodEquiv :
      {g : alpha → beta //
        (∀ a, q (g a) = h a) ∧
        ∀ b, Fintype.card {a // g a = b} = k b} ≃
      {G : ∀ i, A i → B i //
        ∀ i b, Fintype.card {a // G i a = b} = K i b} := {
    toFun g := by
      let gs : {g : alpha → beta // ∀ a, q (g a) = h a} :=
        ⟨g.1, g.2.1⟩
      refine ⟨sectionEquiv gs, ?_⟩
      intro i b
      rw [hfiber gs i b]
      exact g.2.2 b.1
    invFun G := by
      let gs := sectionEquiv.symm G.1
      refine ⟨gs.1, gs.2, ?_⟩
      intro b
      let bi : B (q b) := ⟨b, rfl⟩
      have hb := G.2 (q b) bi
      have hsec : sectionEquiv gs = G.1 :=
        sectionEquiv.apply_symm_apply G.1
      rw [← hsec] at hb
      rw [hfiber gs (q b) bi] at hb
      simpa only [K, bi] using hb
    left_inv g := by
      apply Subtype.ext
      change
        (sectionEquiv.symm (sectionEquiv
          (⟨g.1, g.2.1⟩ : {g : alpha → beta // ∀ a, q (g a) = h a}))).1 = g.1
      exact congrArg Subtype.val
        (sectionEquiv.left_inv ⟨g.1, g.2.1⟩)
    right_inv G := by
      apply Subtype.ext
      exact sectionEquiv.right_inv G.1
  }

  let splitEquiv :
      {G : ∀ i, A i → B i //
        ∀ i b, Fintype.card {a // G i a = b} = K i b} ≃
      ∀ i, {g : A i → B i //
        ∀ b, Fintype.card {a // g a = b} = K i b} := {
    toFun G i := ⟨G.1 i, G.2 i⟩
    invFun G := ⟨fun i => (G i).1, fun i => (G i).2⟩
    left_inv G := by rfl
    right_inv G := by
      funext i
      exact Subtype.ext rfl
  }
  rw [Nat.card_eq_fintype_card, Fintype.card_congr goodEquiv,
    Fintype.card_congr splitEquiv, Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro i hi
  simpa only [A, B, K] using
    (mme_fintype_prescribed_fiber_function_card (K i) (by
      simpa only [A, B, K] using hsum i))

-- Accepted source by marwahaha; submission 3edc90da-2ae9-492d-a365-d0773024ca97.





open BigOperators MME

set_option autoImplicit false
set_option maxHeartbeats 2000000

private def q6AtomMode (u : Fin 4) : Fin 3 → Fin 3 :=
  if u = 0 then ![0, 0, 0]
  else if u = 1 then ![1, 1, 1]
  else if u = 2 then ![0, 1, 2]
  else ![1, 0, 2]

private def q6Decode {N : ℕ} (t : Fin (2 * N) → Fin 4) :
    CWQ6CoupledAddress N :=
  fun i j => q6AtomMode (t j) i

private def q6Encode {N : ℕ} (a : CWQ6CoupledAddress N) :
    Fin (2 * N) → Fin 4 := fun j =>
  if a 2 j = 0 then 0
  else if a 2 j = 1 then 1
  else if a 0 j = 0 then 2
  else 3

private theorem q6AtomMode_encode
    {N : ℕ} (a : CWQ6CoupledAddress N)
    (ha : CWQ6CoupledCoordinatewiseSupported a) :
    q6Decode (q6Encode a) = a := by
  funext i j
  rcases ha j with h | h | h | h
  all_goals rcases h with ⟨h0, h1, h2⟩
  all_goals fin_cases i <;> simp [q6Decode, q6Encode, q6AtomMode, h0, h1, h2]

private theorem q6Encode_decode
    {N : ℕ} (t : Fin (2 * N) → Fin 4) :
    q6Encode (q6Decode t) = t := by
  funext j
  generalize hu : t j = u
  fin_cases u <;> simp [q6Encode, q6Decode, q6AtomMode, hu]

private theorem q6Decode_supported
    {N : ℕ} (t : Fin (2 * N) → Fin 4) :
    CWQ6CoupledCoordinatewiseSupported (q6Decode t) := by
  intro j
  generalize hu : t j = u
  fin_cases u <;> simp [q6Decode, q6AtomMode, hu]

private def q6AtomMultiplicity (L G : ℕ) (u : Fin 4) : ℕ :=
  if u = 0 then L else if u = 1 then L else G

private theorem card_filter_two_values
    {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]
    (t : α → β) (r s : β) (hrs : r ≠ s) :
    ((Finset.univ : Finset α).filter (fun j => t j = r ∨ t j = s)).card =
      ((Finset.univ : Finset α).filter (fun j => t j = r)).card +
        ((Finset.univ : Finset α).filter (fun j => t j = s)).card := by
  rw [Finset.filter_or, Finset.card_union_of_disjoint]
  rw [Finset.disjoint_left]
  intro j hjr hjs
  have hr := (Finset.mem_filter.mp hjr).2
  have hs := (Finset.mem_filter.mp hjs).2
  exact hrs (hr.symm.trans hs)

private theorem q6Encode_profile
    {N L G : ℕ} (hLG : L + G = N)
    (a : CWQ6CoupledAddress N)
    (hsupp : CWQ6CoupledCoordinatewiseSupported a)
    (hmarg : ∀ i r : Fin 3,
      ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j => a i j = r)).card =
          cwQ6CoupledMarginalMultiplicity N L G i r) :
    ∀ u : Fin 4,
      ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j => q6Encode a j = u)).card = q6AtomMultiplicity L G u := by
  intro u
  fin_cases u
  · have hset :
        ((Finset.univ : Finset (Fin (2 * N))).filter
          (fun j => q6Encode a j = 0)) =
        Finset.univ.filter (fun j => a 2 j = 0) := by
      ext j
      rcases hsupp j with h | h | h | h
      all_goals rcases h with ⟨h0, h1, h2⟩
      all_goals simp [q6Encode, h0, h2]
    change ((Finset.univ : Finset (Fin (2 * N))).filter
      (fun j => q6Encode a j = 0)).card = q6AtomMultiplicity L G 0
    rw [hset, hmarg 2 0]
    simp [cwQ6CoupledMarginalMultiplicity, q6AtomMultiplicity]
  · have hset :
        ((Finset.univ : Finset (Fin (2 * N))).filter
          (fun j => q6Encode a j = 1)) =
        Finset.univ.filter (fun j => a 2 j = 1) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hsupp j with h | h | h | h
      all_goals rcases h with ⟨h0, h1, h2⟩
      all_goals simp [q6Encode, h0, h2]
    change ((Finset.univ : Finset (Fin (2 * N))).filter
      (fun j => q6Encode a j = 1)).card = q6AtomMultiplicity L G 1
    rw [hset, hmarg 2 1]
    simp [cwQ6CoupledMarginalMultiplicity, q6AtomMultiplicity]
  · let X0 : Finset (Fin (2 * N)) :=
      Finset.univ.filter (fun j => a 0 j = 0)
    let Z0 : Finset (Fin (2 * N)) :=
      Finset.univ.filter (fun j => a 2 j = 0)
    have hsub : Z0 ⊆ X0 := by
      intro j hj
      have hjz := (Finset.mem_filter.mp hj).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases hsupp j with h | h | h | h
      all_goals rcases h with ⟨h0, h1, h2⟩
      all_goals simp_all
    have hset :
        ((Finset.univ : Finset (Fin (2 * N))).filter
          (fun j => q6Encode a j = 2)) = X0 \ Z0 := by
      ext j
      simp only [X0, Z0, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hsupp j with h | h | h | h
      all_goals rcases h with ⟨h0, h1, h2⟩
      all_goals simp [q6Encode, X0, Z0, h0, h2]
    have hsplit := Finset.card_sdiff_add_card_eq_card hsub
    have hx := hmarg 0 0
    have hz := hmarg 2 0
    change X0.card = N at hx
    change Z0.card = L at hz
    change ((Finset.univ : Finset (Fin (2 * N))).filter
      (fun j => q6Encode a j = 2)).card = q6AtomMultiplicity L G 2
    rw [hset]
    simp [q6AtomMultiplicity]
    omega
  · let X1 : Finset (Fin (2 * N)) :=
      Finset.univ.filter (fun j => a 0 j = 1)
    let Z1 : Finset (Fin (2 * N)) :=
      Finset.univ.filter (fun j => a 2 j = 1)
    have hsub : Z1 ⊆ X1 := by
      intro j hj
      have hjz := (Finset.mem_filter.mp hj).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases hsupp j with h | h | h | h
      all_goals rcases h with ⟨h0, h1, h2⟩
      all_goals simp_all
    have hset :
        ((Finset.univ : Finset (Fin (2 * N))).filter
          (fun j => q6Encode a j = 3)) = X1 \ Z1 := by
      ext j
      simp only [X1, Z1, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hsupp j with h | h | h | h
      all_goals rcases h with ⟨h0, h1, h2⟩
      all_goals simp [q6Encode, X1, Z1, h0, h2]
    have hsplit := Finset.card_sdiff_add_card_eq_card hsub
    have hx := hmarg 0 1
    have hz := hmarg 2 1
    change X1.card = N at hx
    change Z1.card = L at hz
    change ((Finset.univ : Finset (Fin (2 * N))).filter
      (fun j => q6Encode a j = 3)).card = q6AtomMultiplicity L G 3
    rw [hset]
    simp [q6AtomMultiplicity]
    omega

private theorem q6Decode_marginals
    {N L G : ℕ} (hLG : L + G = N)
    (t : Fin (2 * N) → Fin 4)
    (hprof : ∀ u : Fin 4,
      ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j => t j = u)).card = q6AtomMultiplicity L G u) :
    ∀ i r : Fin 3,
      ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j => q6Decode t i j = r)).card =
          cwQ6CoupledMarginalMultiplicity N L G i r := by
  have hpair (u v : Fin 4) (huv : u ≠ v) :
      ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j => t j = u ∨ t j = v)).card =
          q6AtomMultiplicity L G u + q6AtomMultiplicity L G v := by
    rw [card_filter_two_values t u v huv, hprof u, hprof v]
  intro i r
  fin_cases i <;> fin_cases r
  · have hset :
        ((Finset.univ : Finset (Fin (2 * N))).filter
          (fun j => q6Decode t 0 j = 0)) =
        Finset.univ.filter (fun j => t j = 0 ∨ t j = 2) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      generalize hu : t j = u
      fin_cases u <;> simp [q6Decode, q6AtomMode, hu]
    change ((Finset.univ : Finset (Fin (2 * N))).filter
      (fun j => q6Decode t 0 j = 0)).card =
        cwQ6CoupledMarginalMultiplicity N L G 0 0
    rw [hset, hpair 0 2 (by decide)]
    simp [q6AtomMultiplicity, cwQ6CoupledMarginalMultiplicity, hLG]
  · have hset :
        ((Finset.univ : Finset (Fin (2 * N))).filter
          (fun j => q6Decode t 0 j = 1)) =
        Finset.univ.filter (fun j => t j = 1 ∨ t j = 3) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      generalize hu : t j = u
      fin_cases u <;> simp [q6Decode, q6AtomMode, hu]
    change ((Finset.univ : Finset (Fin (2 * N))).filter
      (fun j => q6Decode t 0 j = 1)).card =
        cwQ6CoupledMarginalMultiplicity N L G 0 1
    rw [hset, hpair 1 3 (by decide)]
    simp [q6AtomMultiplicity, cwQ6CoupledMarginalMultiplicity, hLG]
  · have hset :
        ((Finset.univ : Finset (Fin (2 * N))).filter
          (fun j => q6Decode t 0 j = 2)) = ∅ := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      generalize hu : t j = u
      fin_cases u <;> simp [q6Decode, q6AtomMode, hu]
    change ((Finset.univ : Finset (Fin (2 * N))).filter
      (fun j => q6Decode t 0 j = 2)).card =
        cwQ6CoupledMarginalMultiplicity N L G 0 2
    rw [hset]
    simp [cwQ6CoupledMarginalMultiplicity]
  · have hset :
        ((Finset.univ : Finset (Fin (2 * N))).filter
          (fun j => q6Decode t 1 j = 0)) =
        Finset.univ.filter (fun j => t j = 0 ∨ t j = 3) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      generalize hu : t j = u
      fin_cases u <;> simp [q6Decode, q6AtomMode, hu]
    change ((Finset.univ : Finset (Fin (2 * N))).filter
      (fun j => q6Decode t 1 j = 0)).card =
        cwQ6CoupledMarginalMultiplicity N L G 1 0
    rw [hset, hpair 0 3 (by decide)]
    simp [q6AtomMultiplicity, cwQ6CoupledMarginalMultiplicity, hLG]
  · have hset :
        ((Finset.univ : Finset (Fin (2 * N))).filter
          (fun j => q6Decode t 1 j = 1)) =
        Finset.univ.filter (fun j => t j = 1 ∨ t j = 2) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      generalize hu : t j = u
      fin_cases u <;> simp [q6Decode, q6AtomMode, hu]
    change ((Finset.univ : Finset (Fin (2 * N))).filter
      (fun j => q6Decode t 1 j = 1)).card =
        cwQ6CoupledMarginalMultiplicity N L G 1 1
    rw [hset, hpair 1 2 (by decide)]
    simp [q6AtomMultiplicity, cwQ6CoupledMarginalMultiplicity, hLG]
  · have hset :
        ((Finset.univ : Finset (Fin (2 * N))).filter
          (fun j => q6Decode t 1 j = 2)) = ∅ := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      generalize hu : t j = u
      fin_cases u <;> simp [q6Decode, q6AtomMode, hu]
    change ((Finset.univ : Finset (Fin (2 * N))).filter
      (fun j => q6Decode t 1 j = 2)).card =
        cwQ6CoupledMarginalMultiplicity N L G 1 2
    rw [hset]
    simp [cwQ6CoupledMarginalMultiplicity]
  · have hset :
        ((Finset.univ : Finset (Fin (2 * N))).filter
          (fun j => q6Decode t 2 j = 0)) =
        Finset.univ.filter (fun j => t j = 0) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      generalize hu : t j = u
      fin_cases u <;> simp [q6Decode, q6AtomMode, hu]
    change ((Finset.univ : Finset (Fin (2 * N))).filter
      (fun j => q6Decode t 2 j = 0)).card =
        cwQ6CoupledMarginalMultiplicity N L G 2 0
    rw [hset, hprof 0]
    simp [q6AtomMultiplicity, cwQ6CoupledMarginalMultiplicity]
  · have hset :
        ((Finset.univ : Finset (Fin (2 * N))).filter
          (fun j => q6Decode t 2 j = 1)) =
        Finset.univ.filter (fun j => t j = 1) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      generalize hu : t j = u
      fin_cases u <;> simp [q6Decode, q6AtomMode, hu]
    change ((Finset.univ : Finset (Fin (2 * N))).filter
      (fun j => q6Decode t 2 j = 1)).card =
        cwQ6CoupledMarginalMultiplicity N L G 2 1
    rw [hset, hprof 1]
    simp [q6AtomMultiplicity, cwQ6CoupledMarginalMultiplicity]
  · have hset :
        ((Finset.univ : Finset (Fin (2 * N))).filter
          (fun j => q6Decode t 2 j = 2)) =
        Finset.univ.filter (fun j => t j = 2 ∨ t j = 3) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      generalize hu : t j = u
      fin_cases u <;> simp [q6Decode, q6AtomMode, hu]
    change ((Finset.univ : Finset (Fin (2 * N))).filter
      (fun j => q6Decode t 2 j = 2)).card =
        cwQ6CoupledMarginalMultiplicity N L G 2 2
    rw [hset, hpair 2 3 (by decide)]
    simp [q6AtomMultiplicity, cwQ6CoupledMarginalMultiplicity]
    omega

private def Q6AtomProfile (N L G : ℕ) : Type :=
  {t : Fin (2 * N) → Fin 4 // ∀ u : Fin 4,
    ((Finset.univ : Finset (Fin (2 * N))).filter
      (fun j => t j = u)).card = q6AtomMultiplicity L G u}

private noncomputable instance q6CoupledAddressFintype (N : ℕ) :
    Fintype (CWQ6CoupledAddress N) :=
  inferInstanceAs (Fintype (Fin 3 → Fin (2 * N) → Fin 3))

private noncomputable instance q6ExactCoupledAddressFintype
    (N L G : ℕ) : Fintype (CWQ6ExactCoupledAddress N L G) :=
  by
    classical
    unfold CWQ6ExactCoupledAddress
    infer_instance

private noncomputable instance q6AtomProfileFintype
    (N L G : ℕ) : Fintype (Q6AtomProfile N L G) :=
  by
    classical
    unfold Q6AtomProfile
    infer_instance

private noncomputable def q6ExactAtomEquiv
    {N L G : ℕ} (hLG : L + G = N) :
    CWQ6ExactCoupledAddress N L G ≃ Q6AtomProfile N L G where
  toFun a := ⟨q6Encode a.1, q6Encode_profile hLG a.1 a.2.1 a.2.2⟩
  invFun t := ⟨q6Decode t.1, q6Decode_supported t.1,
    q6Decode_marginals hLG t.1 t.2⟩
  left_inv a := Subtype.ext (q6AtomMode_encode a.1 a.2.1)
  right_inv t := Subtype.ext (q6Encode_decode t.1)

private theorem q6ExactAddresses_card_eq_fintype
    (N L G : ℕ) :
    (cwQ6ExactAddresses N L G).card =
      Fintype.card (CWQ6ExactCoupledAddress N L G) := by
  classical
  change
    ((Finset.univ : Finset (CWQ6CoupledAddress N)).filter (fun a =>
      CWQ6CoupledCoordinatewiseSupported a ∧
        ∀ i r : Fin 3,
          (Finset.univ.filter (fun j : Fin (2 * N) => a i j = r)).card =
            cwQ6CoupledMarginalMultiplicity N L G i r)).card = _
  symm
  exact Fintype.card_subtype _

private theorem q6AtomProfile_card_multinomial
    {N L G : ℕ} (hLG : L + G = N) :
    Fintype.card (Q6AtomProfile N L G) =
      Nat.multinomial (Finset.univ : Finset (Fin 4))
        (q6AtomMultiplicity L G) := by
  have hsum' : ∑ u : Fin 4, q6AtomMultiplicity L G u = 2 * N := by
    simp [Fin.sum_univ_four, q6AtomMultiplicity]
    omega
  have hsum : ∑ u : Fin 4, q6AtomMultiplicity L G u =
      Fintype.card (Fin (2 * N)) := by simpa using hsum'
  have h := mme_fintype_prescribed_fiber_function_card
    (q6AtomMultiplicity L G) hsum
  have hfiber (t : Fin (2 * N) → Fin 4) (u : Fin 4) :
      Fintype.card {j : Fin (2 * N) // t j = u} =
        ((Finset.univ : Finset (Fin (2 * N))).filter
          (fun j => t j = u)).card := by
    exact Fintype.card_subtype _
  simp_rw [hfiber] at h
  rw [Nat.multinomial, hsum']
  change Fintype.card (Q6AtomProfile N L G) = _ at h
  simpa using h

private theorem q6AtomProfile_card
    {N L G : ℕ} (hLG : L + G = N) :
    Fintype.card (Q6AtomProfile N L G) =
      (Nat.choose (2 * N) L * Nat.choose (2 * N - L) L) *
        Nat.choose (2 * G) G := by
  rw [q6AtomProfile_card_multinomial hLG]
  have huniv : (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} := by
    decide
  rw [huniv]
  rw [Nat.multinomial_insert (a := (0 : Fin 4)) (s := {1, 2, 3})
    (by decide) (q6AtomMultiplicity L G)]
  rw [Nat.multinomial_insert (a := (1 : Fin 4)) (s := {2, 3})
    (by decide) (q6AtomMultiplicity L G)]
  rw [Nat.binomial_eq_choose (a := (2 : Fin 4)) (b := 3)
    (f := q6AtomMultiplicity L G) (by decide)]
  simp [q6AtomMultiplicity]
  have htwon : L + (L + (G + G)) = 2 * N := by omega
  have hrest : L + (G + G) = 2 * N - L := by omega
  have htwoG : G + G = 2 * G := by omega
  rw [htwon, hrest, htwoG]
  simp [Nat.mul_assoc]

private theorem q6ExactAddresses_card
    {N L G : ℕ} (hLG : L + G = N) :
    (cwQ6ExactAddresses N L G).card =
      (Nat.choose (2 * N) L * Nat.choose (2 * N - L) L) *
        Nat.choose (2 * G) G := by
  rw [q6ExactAddresses_card_eq_fintype]
  rw [Fintype.card_congr (q6ExactAtomEquiv hLG)]
  exact q6AtomProfile_card hLG

private def q6AtomsAt (i r : Fin 3) : Finset (Fin 4) :=
  Finset.univ.filter (fun u => q6AtomMode u i = r)

private def q6AtomFactorialDenominator
    (L G : ℕ) (i r : Fin 3) : ℕ :=
  if i = 2 then
    if r = 0 then L.factorial
    else if r = 1 then L.factorial
    else G.factorial * G.factorial
  else if r = 0 then L.factorial * G.factorial
  else if r = 1 then L.factorial * G.factorial
  else 1

private theorem q6AtomFiberMultiplicity_sum
    (N L G : ℕ) (hLG : L + G = N) (i r : Fin 3) :
    (∑ u : {u : Fin 4 // q6AtomMode u i = r},
      q6AtomMultiplicity L G u.1) =
        cwQ6CoupledMarginalMultiplicity N L G i r := by
  rw [← Finset.sum_subtype (q6AtomsAt i r)
    (by intro u; simp [q6AtomsAt]) (q6AtomMultiplicity L G)]
  fin_cases i <;> fin_cases r <;>
    simp only [q6AtomsAt, Finset.sum_filter, Fin.sum_univ_four] <;>
    simp [q6AtomMode, q6AtomMultiplicity,
      cwQ6CoupledMarginalMultiplicity] <;> omega

private theorem q6AtomFiberFactorial_prod
    (L G : ℕ) (i r : Fin 3) :
    (∏ u : {u : Fin 4 // q6AtomMode u i = r},
      (q6AtomMultiplicity L G u.1).factorial) =
        q6AtomFactorialDenominator L G i r := by
  rw [← Finset.prod_subtype (q6AtomsAt i r)
    (by intro u; simp [q6AtomsAt])
    (fun u => (q6AtomMultiplicity L G u).factorial)]
  fin_cases i <;> fin_cases r <;>
    simp only [q6AtomsAt, Finset.prod_filter, Fin.prod_univ_four] <;>
    simp [q6AtomMode, q6AtomMultiplicity,
      q6AtomFactorialDenominator]

private theorem mem_q6ExactAddresses_iff
    {N L G : ℕ} (a : CWQ6CoupledAddress N) :
    a ∈ cwQ6ExactAddresses N L G ↔
      CWQ6CoupledCoordinatewiseSupported a ∧
        ∀ i r : Fin 3,
          (Finset.univ.filter (fun j : Fin (2 * N) => a i j = r)).card =
            cwQ6CoupledMarginalMultiplicity N L G i r := by
  classical
  simp [cwQ6ExactAddresses]

private def Q6AtomProfileOver
    (N L G : ℕ) (i : Fin 3) (w : Fin (2 * N) → Fin 3) : Type :=
  {t : Fin (2 * N) → Fin 4 //
    (∀ j, q6AtomMode (t j) i = w j) ∧
      ∀ u : Fin 4,
        Fintype.card {j : Fin (2 * N) // t j = u} =
          q6AtomMultiplicity L G u}

private noncomputable def q6ExactFinsetFiberEquiv
    {N L G : ℕ} (i : Fin 3) (w : Fin (2 * N) → Fin 3) :
    {a : CWQ6CoupledAddress N //
      a ∈ (cwQ6ExactAddresses N L G).filter (fun e => e i = w)} ≃
    {a : CWQ6ExactCoupledAddress N L G // a.1 i = w} where
  toFun a := by
    have ha := Finset.mem_filter.mp a.2
    exact ⟨⟨a.1, (mem_q6ExactAddresses_iff a.1).mp ha.1⟩, ha.2⟩
  invFun a :=
    ⟨a.1.1, Finset.mem_filter.mpr
      ⟨(mem_q6ExactAddresses_iff a.1.1).mpr a.1.2, a.2⟩⟩
  left_inv a := Subtype.ext rfl
  right_inv a := Subtype.ext (Subtype.ext rfl)

private noncomputable def q6ExactFiberAtomEquiv
    {N L G : ℕ} (hLG : L + G = N)
    (i : Fin 3) (w : Fin (2 * N) → Fin 3) :
    {a : CWQ6ExactCoupledAddress N L G // a.1 i = w} ≃
      Q6AtomProfileOver N L G i w where
  toFun a := by
    refine ⟨q6Encode a.1.1, ?_, ?_⟩
    · intro j
      have hdec := q6AtomMode_encode a.1.1 a.1.2.1
      have hj := congrFun (congrFun hdec i) j
      have hj' : q6AtomMode (q6Encode a.1.1 j) i = a.1.1 i j := by
        simpa [q6Decode] using hj
      exact hj'.trans (congrFun a.2 j)
    · intro u
      exact (Fintype.card_subtype _).trans
        (q6Encode_profile hLG a.1.1 a.1.2.1 a.1.2.2 u)
  invFun t := by
    have hprof : ∀ u : Fin 4,
        ((Finset.univ : Finset (Fin (2 * N))).filter
          (fun j => t.1 j = u)).card = q6AtomMultiplicity L G u := by
      intro u
      exact (Fintype.card_subtype _).symm.trans (t.2.2 u)
    refine ⟨⟨q6Decode t.1, q6Decode_supported t.1,
      q6Decode_marginals hLG t.1 hprof⟩, ?_⟩
    funext j
    exact t.2.1 j
  left_inv a := by
    apply Subtype.ext
    apply Subtype.ext
    exact q6AtomMode_encode a.1.1 a.1.2.1
  right_inv t := Subtype.ext (q6Encode_decode t.1)

private theorem q6AtomProfileOver_card_formula
    {N L G : ℕ} (hLG : L + G = N)
    (i : Fin 3) (w : Fin (2 * N) → Fin 3)
    (hw : ∀ r : Fin 3,
      ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j => w j = r)).card =
          cwQ6CoupledMarginalMultiplicity N L G i r) :
    Nat.card (Q6AtomProfileOver N L G i w) =
      ∏ r : Fin 3,
        (cwQ6CoupledMarginalMultiplicity N L G i r).factorial /
          q6AtomFactorialDenominator L G i r := by
  have hsum (r : Fin 3) :
      (∑ u : {u : Fin 4 // q6AtomMode u i = r},
        q6AtomMultiplicity L G u.1) =
          Fintype.card {j : Fin (2 * N) // w j = r} := by
    rw [q6AtomFiberMultiplicity_sum N L G hLG i r]
    exact ((Fintype.card_subtype _).trans (hw r)).symm
  have h := mme_fintype_constrained_prescribed_fiber_function_card
    w (fun u : Fin 4 => q6AtomMode u i) (q6AtomMultiplicity L G) hsum
  change Nat.card (Q6AtomProfileOver N L G i w) = _ at h
  have hwcard (r : Fin 3) :
      Fintype.card {j : Fin (2 * N) // w j = r} =
        cwQ6CoupledMarginalMultiplicity N L G i r :=
    (Fintype.card_subtype _).trans (hw r)
  simp_rw [hwcard, q6AtomFiberFactorial_prod] at h
  exact h

private theorem q6AtomProfileOver_card
    {N L G : ℕ} (hLG : L + G = N)
    (i : Fin 3) (w : Fin (2 * N) → Fin 3)
    (hw : ∀ r : Fin 3,
      ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j => w j = r)).card =
          cwQ6CoupledMarginalMultiplicity N L G i r) :
    Nat.card (Q6AtomProfileOver N L G i w) =
      if i = 2 then Nat.choose (2 * G) G else (Nat.choose N G) ^ 2 := by
  have h := q6AtomProfileOver_card_formula hLG i w hw
  have hchooseN : Nat.choose N G =
      N.factorial / (L.factorial * G.factorial) := by
    rw [← hLG]
    exact Nat.add_choose L G
  have hchooseG : Nat.choose (2 * G) G =
      (2 * G).factorial / (G.factorial * G.factorial) := by
    rw [show 2 * G = G + G by omega]
    exact Nat.add_choose G G
  have hfacL : L.factorial / L.factorial = 1 :=
    Nat.div_self (Nat.factorial_pos L)
  fin_cases i
  · simpa [Fin.prod_univ_three, cwQ6CoupledMarginalMultiplicity,
      q6AtomFactorialDenominator, hchooseN, pow_two] using h
  · simpa [Fin.prod_univ_three, cwQ6CoupledMarginalMultiplicity,
      q6AtomFactorialDenominator, hchooseN, pow_two] using h
  · simpa [Fin.prod_univ_three, cwQ6CoupledMarginalMultiplicity,
      q6AtomFactorialDenominator, hchooseG,
      hfacL] using h

private theorem q6ExactFiber_card
    {N L G : ℕ} (hLG : L + G = N)
    (i : Fin 3) (w : Fin (2 * N) → Fin 3)
    (hw : ∀ r : Fin 3,
      ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j => w j = r)).card =
          cwQ6CoupledMarginalMultiplicity N L G i r) :
    ((cwQ6ExactAddresses N L G).filter (fun e => e i = w)).card =
      if i = 2 then Nat.choose (2 * G) G else (Nat.choose N G) ^ 2 := by
  let S : Finset (CWQ6CoupledAddress N) :=
    (cwQ6ExactAddresses N L G).filter
      (fun e : CWQ6CoupledAddress N => e i = w)
  change S.card = _
  calc
    S.card = Fintype.card ↑S := (Fintype.card_coe S).symm
    _ = Nat.card ↑S := by
      rw [Nat.card_eq_fintype_card]
    _ = Nat.card {a : CWQ6ExactCoupledAddress N L G // a.1 i = w} :=
      Nat.card_congr (by
        simpa only [S] using q6ExactFinsetFiberEquiv (L := L) (G := G) i w)
    _ = Nat.card (Q6AtomProfileOver N L G i w) :=
      Nat.card_congr (q6ExactFiberAtomEquiv hLG i w)
    _ = _ := q6AtomProfileOver_card hLG i w hw

private theorem q6_choose_factorization
    {N L G : ℕ} (hLG : L + G = N) :
    (Nat.choose (2 * N) L * Nat.choose (2 * N - L) L) *
        Nat.choose (2 * G) G =
      Nat.choose (2 * N) N * (Nat.choose N G) ^ 2 := by
  have hLle : L ≤ 2 * N := by omega
  have hLrest : L ≤ 2 * N - L := by omega
  have hGle : G ≤ N := by omega
  have hNle : N ≤ 2 * N := by omega
  have hrest : 2 * N - L - L = 2 * G := by omega
  have hNG : N - G = L := by omega
  have hGG : 2 * G - G = G := by omega
  have hNN : 2 * N - N = N := by omega
  have h1 := Nat.choose_mul_factorial_mul_factorial hLle
  have h2 := Nat.choose_mul_factorial_mul_factorial hLrest
  have h3 := Nat.choose_mul_factorial_mul_factorial (show G ≤ 2 * G by omega)
  have h4 := Nat.choose_mul_factorial_mul_factorial hNle
  have h5 := Nat.choose_mul_factorial_mul_factorial hGle
  change Nat.choose (2 * N) L * L.factorial * (2 * N - L).factorial =
    (2 * N).factorial at h1
  change Nat.choose (2 * N - L) L * L.factorial *
    (2 * N - L - L).factorial = (2 * N - L).factorial at h2
  rw [hrest] at h2
  rw [hGG] at h3
  change Nat.choose (2 * G) G * G.factorial * G.factorial =
    (2 * G).factorial at h3
  rw [hNN] at h4
  change Nat.choose (2 * N) N * N.factorial * N.factorial =
    (2 * N).factorial at h4
  change Nat.choose N G * G.factorial * (N - G).factorial =
    N.factorial at h5
  rw [hNG] at h5
  let D := L.factorial * L.factorial * G.factorial * G.factorial
  have hleft :
      ((Nat.choose (2 * N) L * Nat.choose (2 * N - L) L) *
          Nat.choose (2 * G) G) * D = (2 * N).factorial := by
    dsimp [D]
    calc
      _ = Nat.choose (2 * N) L * L.factorial *
          (Nat.choose (2 * N - L) L * L.factorial *
            (Nat.choose (2 * G) G * G.factorial * G.factorial)) := by ring
      _ = Nat.choose (2 * N) L * L.factorial *
          (Nat.choose (2 * N - L) L * L.factorial *
            (2 * G).factorial) := by rw [h3]
      _ = Nat.choose (2 * N) L * L.factorial *
          (2 * N - L).factorial := by rw [h2]
      _ = (2 * N).factorial := h1
  have hright :
      (Nat.choose (2 * N) N * (Nat.choose N G) ^ 2) * D =
        (2 * N).factorial := by
    dsimp [D]
    calc
      _ = Nat.choose (2 * N) N *
          (Nat.choose N G * G.factorial * L.factorial) *
          (Nat.choose N G * G.factorial * L.factorial) := by ring
      _ = Nat.choose (2 * N) N * N.factorial * N.factorial := by
        rw [h5]
      _ = (2 * N).factorial := h4
  exact Nat.eq_of_mul_eq_mul_right (by positivity : 0 < D)
    (hleft.trans hright.symm)

private theorem q6ModeWord_marginals
    {N L G : ℕ} (i : Fin 3) (w : Fin (2 * N) → Fin 3)
    (hw : w ∈ (cwQ6ExactAddresses N L G).image (fun e => e i)) :
    ∀ r : Fin 3,
      ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j => w j = r)).card =
          cwQ6CoupledMarginalMultiplicity N L G i r := by
  classical
  rcases Finset.mem_image.mp hw with ⟨a, ha, hai⟩
  intro r
  rw [← hai]
  exact ((mem_q6ExactAddresses_iff a).mp ha).2 i r

private theorem q6ModeWords_card
    {N L G : ℕ} (hLG : L + G = N) (i : Fin 3) :
    ((cwQ6ExactAddresses N L G).image (fun e => e i)).card =
      if i = 2 then
        Nat.choose (2 * N) L * Nat.choose (2 * N - L) L
      else Nat.choose (2 * N) N := by
  classical
  let A := cwQ6ExactAddresses N L G
  let W := A.image (fun e => e i)
  have hdegree (w : Fin (2 * N) → Fin 3) (hw : w ∈ W) :
      (A.filter (fun e => e i = w)).card =
        if i = 2 then Nat.choose (2 * G) G else (Nat.choose N G) ^ 2 := by
    apply q6ExactFiber_card hLG i w
    exact q6ModeWord_marginals i w (by simpa [A, W] using hw)
  have hsum := Finset.card_eq_sum_card_image (fun e : CWQ6CoupledAddress N => e i) A
  have hconst :
      (∑ w ∈ W, (A.filter (fun e => e i = w)).card) =
        W.card * (if i = 2 then Nat.choose (2 * G) G
          else (Nat.choose N G) ^ 2) :=
    Finset.sum_const_nat hdegree
  change A.card = ∑ w ∈ W, (A.filter (fun e => e i = w)).card at hsum
  rw [hconst] at hsum
  fin_cases i
  · have hpos : 0 < (Nat.choose N G) ^ 2 := by
      have : 0 < Nat.choose N G := Nat.choose_pos (by omega)
      positivity
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc
      W.card * (Nat.choose N G) ^ 2 = A.card := by simpa using hsum.symm
      _ = (Nat.choose (2 * N) L * Nat.choose (2 * N - L) L) *
          Nat.choose (2 * G) G := by simpa [A] using q6ExactAddresses_card hLG
      _ = Nat.choose (2 * N) N * (Nat.choose N G) ^ 2 :=
        q6_choose_factorization hLG
  · have hpos : 0 < (Nat.choose N G) ^ 2 := by
      have : 0 < Nat.choose N G := Nat.choose_pos (by omega)
      positivity
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc
      W.card * (Nat.choose N G) ^ 2 = A.card := by simpa using hsum.symm
      _ = (Nat.choose (2 * N) L * Nat.choose (2 * N - L) L) *
          Nat.choose (2 * G) G := by simpa [A] using q6ExactAddresses_card hLG
      _ = Nat.choose (2 * N) N * (Nat.choose N G) ^ 2 :=
        q6_choose_factorization hLG
  · have hpos : 0 < Nat.choose (2 * G) G :=
      Nat.choose_pos (by omega)
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc
      W.card * Nat.choose (2 * G) G = A.card := by simpa using hsum.symm
      _ = (Nat.choose (2 * N) L * Nat.choose (2 * N - L) L) *
          Nat.choose (2 * G) G := by simpa [A] using q6ExactAddresses_card hLG

theorem mme_CW_q6_exact_coupled_address_regularity
    (N L G : ℕ) (hLG : L + G = N) :
    CWQ6ExactAddressRegularity N L G := by
  classical
  refine ⟨q6ExactAddresses_card hLG, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [cwQ6ExactXWords] using
      q6ModeWords_card hLG (0 : Fin 3)
  · simpa [cwQ6ExactYWords] using
      q6ModeWords_card hLG (1 : Fin 3)
  · simpa [cwQ6ExactZWords] using
      q6ModeWords_card hLG (2 : Fin 3)
  · intro x hx
    have hx' : x ∈ (cwQ6ExactAddresses N L G).image (fun e => e 0) := by
      simpa [cwQ6ExactXWords] using hx
    simpa using q6ExactFiber_card hLG (0 : Fin 3) x
      (q6ModeWord_marginals 0 x hx')
  · intro y hy
    have hy' : y ∈ (cwQ6ExactAddresses N L G).image (fun e => e 1) := by
      simpa [cwQ6ExactYWords] using hy
    simpa using q6ExactFiber_card hLG (1 : Fin 3) y
      (q6ModeWord_marginals 1 y hy')
  · intro z hz
    have hz' : z ∈ (cwQ6ExactAddresses N L G).image (fun e => e 2) := by
      simpa [cwQ6ExactZWords] using hz
    simpa using q6ExactFiber_card hLG (2 : Fin 3) z
      (q6ModeWord_marginals 2 z hz')

theorem factorization {N L G : ℕ} (hLG : L + G = N) :
    (Nat.choose (2 * N) L * Nat.choose (2 * N - L) L) * Nat.choose (2 * G) G =
      Nat.choose (2 * N) N * (Nat.choose N G) ^ 2 := q6_choose_factorization hLG

end PruningClosure

#print axioms PruningClosure.mme_CW_q6_exact_coupled_address_regularity
#print axioms PruningClosure.factorization

-- End complete component: Closure.lean

-- Begin complete component: Analytic.lean


set_option autoImplicit false

open Filter

namespace IsolatedMassCounterexample

theorem dense_AP_for_polynomial_modulus (k : ℕ) (C : ℝ) (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop, ∀ M : ℕ, 3 ≤ M → (M : ℝ) ≤ C * (n : ℝ) ^ k →
      ∃ S : Finset ℕ, S ⊆ Finset.range (M / 2) ∧ ThreeAPFree (S : Set ℕ) ∧
        0 < S.card ∧ 1 / (n : ℝ) ≤ (S.card : ℝ) / (M : ℝ) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually_ge_atTop
    (max 1 (max (2 * Real.log 3) (max (128 * (k : ℝ)) (128 * |Real.log C|)))),
    eventually_ge_atTop (1 : ℕ)] with n hnlog hn
  simp only [max_le_iff] at hnlog
  obtain ⟨hx1, hx3, hxk, hxC⟩ := hnlog
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hx0 : 0 ≤ Real.log (n : ℝ) := by linarith
  intro M hM hbound
  let T := M / 2
  have hT : 1 ≤ T := by dsimp [T]; omega
  have hT0 : 0 < (T : ℝ) := by exact_mod_cast (by omega : 0 < T)
  have hM0 : 0 < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hTM : (T : ℝ) ≤ (M : ℝ) := by exact_mod_cast (Nat.div_le_self M 2)
  have hthird : (M : ℝ) ≤ 3 * (T : ℝ) := by
    exact_mod_cast (by dsimp [T]; omega : M ≤ 3 * T)
  have hlogT : Real.log (T : ℝ) ≤ Real.log C + (k : ℝ) * Real.log (n : ℝ) := by
    calc
      _ ≤ Real.log (C * (n : ℝ) ^ k) := Real.log_le_log hT0 (hTM.trans hbound)
      _ = _ := by rw [Real.log_mul hC.ne' (pow_pos hn0 k).ne', Real.log_pow]
  let q := Real.sqrt (Real.log (T : ℝ))
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hq2 : q ^ 2 = Real.log (T : ℝ) :=
    Real.sq_sqrt (Real.log_nonneg (by exact_mod_cast hT))
  have hxmul : 0 ≤ Real.log (n : ℝ) * (Real.log (n : ℝ) - 128 * (k : ℝ)) :=
    mul_nonneg hx0 (by linarith)
  have hxsq : Real.log (n : ℝ) ≤ Real.log (n : ℝ) ^ 2 := by
    nlinarith [mul_nonneg hx0 (show 0 ≤ Real.log (n : ℝ) - 1 by linarith)]
  have hboundq : 64 * q ^ 2 ≤ Real.log (n : ℝ) ^ 2 := by
    nlinarith [le_abs_self (Real.log C)]
  have hq : 4 * q ≤ Real.log (n : ℝ) / 2 :=
    le_of_sq_le_sq (by nlinarith [hboundq]) (by positivity)
  have hsum : Real.log 3 + 4 * q ≤ Real.log (n : ℝ) := by linarith
  have hexp : 3 * Real.exp (4 * q) ≤ (n : ℝ) := by
    calc
      _ = Real.exp (Real.log 3 + 4 * q) := by
        rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
      _ ≤ Real.exp (Real.log (n : ℝ)) := Real.exp_le_exp.mpr hsum
      _ = _ := Real.exp_log hn0
  have hinv : 3 ≤ (n : ℝ) * Real.exp (-4 * q) := by
    calc
      3 = (3 * Real.exp (4 * q)) * Real.exp (-4 * q) := by
        rw [mul_assoc, ← Real.exp_add]
        ring_nf
        simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hexp (Real.exp_pos _).le
  have hsmall : 1 / (n : ℝ) ≤ Real.exp (-4 * q) / 3 := by
    apply (div_le_iff₀ hn0).mpr
    nlinarith
  obtain ⟨S, hSrange, hScard, hSfree⟩ := rothNumberNat_spec T
  have hmass : (T : ℝ) * Real.exp (-4 * q) ≤ (S.card : ℝ) := by
    rw [hScard]
    exact Behrend.roth_lower_bound
  have hSpos : 0 < S.card := by
    have := (mul_pos hT0 (Real.exp_pos (-4 * q))).trans_le hmass
    exact_mod_cast this
  refine ⟨S, hSrange, hSfree, hSpos, hsmall.trans ?_⟩
  apply (le_div_iff₀ hM0).mpr
  nlinarith [mul_le_mul_of_nonneg_right hthird (Real.exp_pos (-4 * q)).le]

end IsolatedMassCounterexample

#print axioms IsolatedMassCounterexample.dense_AP_for_polynomial_modulus

-- End complete component: Analytic.lean

-- Begin complete component: Counting.lean


set_option autoImplicit false

open MME

namespace IsolatedMassCounterexample

theorem isolated_card_bound {N L G : ℕ} (hreg : CWQ6ExactAddressRegularity N L G)
    (E I : Finset (CWQ6ExactCoupledAddress N L G)) (hIE : I ⊆ E)
    (hiso : ∀ e ∈ I, ∀ e' ∈ E,
      (e.1 0 = e'.1 0 ∨ e.1 1 = e'.1 1) → e = e') :
    I.card ≤ Nat.choose (2 * N) N := by
  classical
  have hinj : Set.InjOn (fun e : CWQ6ExactCoupledAddress N L G => e.1 0) I := by
    intro a ha b hb hab
    exact hiso a ha b (hIE hb) (Or.inl hab)
  calc
    I.card = (I.image (fun e => e.1 0)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (cwQ6ExactXWords N L G).card := by
      apply Finset.card_le_card
      intro w hw
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hw
      apply Finset.mem_image.mpr
      refine ⟨e.1, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.2⟩
    _ = _ := hreg.x_word_card

theorem choose_profile_lower (L n : ℕ) :
    (n : ℝ) ^ L ≤ ((L * (n + 1)).choose (L * n) : ℝ) := by
  have hN : L * (n + 1) = L + L * n := by ring
  rw [← Nat.choose_symm_of_eq_add hN]
  have hfac : (L.factorial : ℝ) ≤ (L : ℝ) ^ L := by
    exact_mod_cast Nat.factorial_le_pow L
  have hfac0 : 0 < (L.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos L
  calc
    (n : ℝ) ^ L ≤ ((L : ℝ) * n) ^ L / (L.factorial : ℝ) := by
      apply (le_div_iff₀ hfac0).mpr
      rw [mul_pow]
      nlinarith [mul_le_mul_of_nonneg_right hfac (pow_nonneg (Nat.cast_nonneg n) L)]
    _ ≤ (((L * (n + 1) + 1 - L : ℕ) : ℝ) ^ L) / (L.factorial : ℝ) := by
      gcongr
      exact_mod_cast (show L * n ≤ L * (n + 1) + 1 - L by omega)
    _ ≤ _ := Nat.pow_le_choose L (L * (n + 1))

theorem modulus_polynomial_bound (L n : ℕ) (hn : 1 ≤ n) :
    ((4 * ((L * (n + 1)).choose (L * n)) ^ 2 + 1 : ℕ) : ℝ) ≤
      (4 * (2 * (L : ℝ)) ^ (2 * L) + 1) * (n : ℝ) ^ (2 * L) := by
  have hN : L * (n + 1) = L + L * n := by ring
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsize : (L * (n + 1) : ℕ) ≤ 2 * L * n := by nlinarith
  have hcast : ((L * (n + 1) : ℕ) : ℝ) ≤ 2 * (L : ℝ) * n := by exact_mod_cast hsize
  have hchoose : ((L * (n + 1)).choose (L * n) : ℝ) ≤
      ((L * (n + 1) : ℕ) : ℝ) ^ L := by
    rw [← Nat.choose_symm_of_eq_add hN]
    exact_mod_cast Nat.choose_le_pow (L * (n + 1)) L
  have hsquare : (((L * (n + 1)).choose (L * n) : ℝ)) ^ 2 ≤
      (2 * (L : ℝ) * n) ^ (2 * L) := by
    calc
      _ ≤ (((L * (n + 1) : ℕ) : ℝ) ^ L) ^ 2 := by gcongr
      _ = (((L * (n + 1) : ℕ) : ℝ)) ^ (2 * L) := by rw [← pow_mul, Nat.mul_comm L 2]
      _ ≤ _ := by gcongr
  have hnpow : (1 : ℝ) ≤ (n : ℝ) ^ (2 * L) := one_le_pow₀ hn1
  push_cast
  rw [mul_pow] at hsquare
  nlinarith

end IsolatedMassCounterexample

#print axioms IsolatedMassCounterexample.isolated_card_bound
#print axioms IsolatedMassCounterexample.choose_profile_lower
#print axioms IsolatedMassCounterexample.modulus_polynomial_bound

-- End complete component: Counting.lean

-- Begin complete component: Final.lean



set_option autoImplicit false

open MME Filter IsolatedMassCounterexample

theorem isolatedMassImpossible : ¬ (∃ d : ℕ, 0 < d ∧
    ∀ (N L G : ℕ), CWQ6ExactAddressRegularity N L G →
      (0 < L ∧ L + G = N ∧ 341 * L < 100 * G) →
      let Zcount : ℕ := Nat.choose (2 * N) L * Nat.choose (2 * N - L) L
      let Xcount : ℕ := Nat.choose N G
      let middle : ℕ := Nat.choose (2 * G) G
      let Mmod : ℕ := 4 * Xcount ^ 2 + 1
      ∀ S : Finset ℕ,
        S ⊆ Finset.range (Mmod / 2) → ThreeAPFree (S : Set ℕ) → 0 < S.card →
        ∃ E I : Finset (CWQ6ExactCoupledAddress N L G), ∃ H : ℕ,
          0 < H ∧ I ⊆ E ∧
          (∀ e ∈ I, ∀ e' ∈ E,
            (e.1 0 = e'.1 0 ∨ e.1 1 = e'.1 1) → e = e') ∧
          (∀ c ∈ I.image (fun e => e.1 2),
            (I.filter (fun e => e.1 2 = c)).card ≤ middle) ∧
          (∀ ex ∈ I, ∀ ey ∈ I, ∀ ez ∈ I,
            CWQ6CoupledCoordinatewiseSupported
                (cwQ6CoupledMixedAddress ex.1 ey.1 ez.1) →
              ∃ e' ∈ E, e'.1 0 = ex.1 0 ∧ e'.1 1 = ey.1 1 ∧ e'.1 2 = ez.1 2) ∧
          H ≤ 4 ^ N ∧
          (middle : ℝ) * ((((S.card : ℝ) / (Mmod : ℝ)) ^ d) /
            (((N + 1 : ℕ) : ℝ) ^ d)) ≤ 4 * (Xcount : ℝ) ^ 2 * (H : ℝ) ∧
          (H : ℝ) * ((I.image (fun e => e.1 2)).card : ℝ) +
              (middle : ℝ) * ((Zcount : ℝ) *
                ((((S.card : ℝ) / (Mmod : ℝ)) ^ d) / (((N + 1 : ℕ) : ℝ) ^ d))) ≤
            (I.card : ℝ)) := by
  classical
  rintro ⟨d, hd, alleged⟩
  let L := d + 1
  let C : ℝ := 4 * (2 * (L : ℝ)) ^ (2 * L) + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hdense := dense_AP_for_polynomial_modulus (2 * L) C hC
  obtain ⟨n, hndense, hn⟩ :=
    (hdense.and (eventually_ge_atTop (max 4 ((2 * L + 1) ^ d + 1)))).exists
  have hn4 : 4 ≤ n := (le_max_left _ _).trans hn
  have hnlarge : (2 * L + 1) ^ d < n := by
    have := (le_max_right 4 ((2 * L + 1) ^ d + 1)).trans hn
    omega
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  let N := L * (n + 1)
  let G := L * n
  let X := Nat.choose N G
  let M := 4 * X ^ 2 + 1
  let B := Nat.choose (2 * N) N
  let Z := Nat.choose (2 * N) L * Nat.choose (2 * N - L) L
  let middle := Nat.choose (2 * G) G
  have hL : 0 < L := by dsimp [L]; omega
  have hLG : L + G = N := by dsimp [N, G]; ring
  have h4L : 4 * L ≤ G := by dsimp [G]; nlinarith
  have hprofile : 0 < L ∧ L + G = N ∧ 341 * L < 100 * G :=
    ⟨hL, hLG, by nlinarith⟩
  have hX : 0 < X := Nat.choose_pos (by omega)
  have hM : 3 ≤ M := by dsimp [M]; nlinarith
  have hMB : (M : ℝ) ≤ C * (n : ℝ) ^ (2 * L) :=
    modulus_polynomial_bound L n (by omega)
  obtain ⟨S, hSrange, hSfree, hSpos, hdensity⟩ := hndense M hM hMB
  have hreg := PruningClosure.mme_CW_q6_exact_coupled_address_regularity N L G hLG
  obtain ⟨E, I, H, hH, hIE, hiso, _hfiber, _hmix, _hHbound, _hmid, hmass⟩ :=
    alleged N L G hreg hprofile S hSrange hSfree hSpos
  have hI := isolated_card_bound hreg E I hIE hiso
  let density : ℝ := (S.card : ℝ) / M
  change 1 / (n : ℝ) ≤ density at hdensity
  change (H : ℝ) * ((I.image (fun e => e.1 2)).card : ℝ) +
      (middle : ℝ) * ((Z : ℝ) * (density ^ d / (((N + 1 : ℕ) : ℝ) ^ d))) ≤
        (I.card : ℝ) at hmass
  have hfactor : (middle : ℝ) * Z = (B : ℝ) * (X : ℝ) ^ 2 := by
    calc
      _ = (Z : ℝ) * middle := mul_comm _ _
      _ = _ := by exact_mod_cast PruningClosure.factorization hLG
  have hB0 : 0 < (B : ℝ) := by
    exact_mod_cast (Nat.choose_pos (by omega : N ≤ 2 * N))
  have hNPow : 0 < (((N + 1 : ℕ) : ℝ) ^ d) := by positivity
  have hcapacity : (B : ℝ) *
      ((X : ℝ) ^ 2 * (density ^ d / (((N + 1 : ℕ) : ℝ) ^ d))) ≤ B := by
    calc
      _ = (middle : ℝ) * ((Z : ℝ) *
          (density ^ d / (((N + 1 : ℕ) : ℝ) ^ d))) := by
        rw [← mul_assoc, ← hfactor, mul_assoc]
      _ ≤ (I.card : ℝ) := by
        have hnonneg : (0 : ℝ) ≤ (H : ℝ) *
            ((I.image (fun e => e.1 2)).card : ℝ) := by positivity
        linarith only [hmass, hnonneg]
      _ ≤ B := by exact_mod_cast hI
  have hquot : (X : ℝ) ^ 2 * (density ^ d / (((N + 1 : ℕ) : ℝ) ^ d)) ≤ 1 := by
    apply (mul_le_mul_iff_right₀ hB0).mp
    simpa only [mul_one] using hcapacity
  have hcap : (X : ℝ) ^ 2 * density ^ d ≤ (((N + 1 : ℕ) : ℝ) ^ d) := by
    have hh : ((X : ℝ) ^ 2 * density ^ d) / (((N + 1 : ℕ) : ℝ) ^ d) ≤ 1 := by
      simpa only [mul_div_assoc] using hquot
    exact (div_le_one hNPow).mp hh
  have hcapSmall : (X : ℝ) ^ 2 / (n : ℝ) ^ d ≤ (((N + 1 : ℕ) : ℝ) ^ d) := by
    calc
      _ = (X : ℝ) ^ 2 * (1 / (n : ℝ)) ^ d := by
        simp only [div_eq_mul_inv, one_mul, inv_pow]
      _ ≤ (X : ℝ) ^ 2 * density ^ d := by gcongr
      _ ≤ _ := hcap
  have hXupper : (X : ℝ) ^ 2 ≤ (((N + 1 : ℕ) : ℝ) ^ d) * (n : ℝ) ^ d :=
    (div_le_iff₀ (pow_pos hn0 d)).mp hcapSmall
  have hNplus : ((N + 1 : ℕ) : ℝ) ≤ (2 * (L : ℝ) + 1) * (n : ℝ) := by
    have hnat : N + 1 ≤ (2 * L + 1) * n := by dsimp [N]; nlinarith
    exact_mod_cast hnat
  have hbig : (X : ℝ) ^ 2 ≤ (2 * (L : ℝ) + 1) ^ d * (n : ℝ) ^ (2 * d) := by
    calc
      _ ≤ (((N + 1 : ℕ) : ℝ) ^ d) * (n : ℝ) ^ d := hXupper
      _ ≤ ((2 * (L : ℝ) + 1) * (n : ℝ)) ^ d * (n : ℝ) ^ d := by gcongr
      _ = _ := by rw [mul_pow, mul_assoc, ← pow_add]; congr 2; omega
  have hXlower : (n : ℝ) ^ L ≤ (X : ℝ) := choose_profile_lower L n
  have hproduct : (n : ℝ) ^ (2 * d) * (n : ℝ) ^ 2 ≤
      (n : ℝ) ^ (2 * d) * (2 * (L : ℝ) + 1) ^ d := by
    calc
      _ = (n : ℝ) ^ (2 * L) := by
        rw [← pow_add, show 2 * d + 2 = 2 * L by dsimp [L]; omega]
      _ = ((n : ℝ) ^ L) ^ 2 := by rw [← pow_mul, Nat.mul_comm L 2]
      _ ≤ (X : ℝ) ^ 2 := by gcongr
      _ ≤ (2 * (L : ℝ) + 1) ^ d * (n : ℝ) ^ (2 * d) := hbig
      _ = _ := mul_comm _ _
  have hsmall : (n : ℝ) ^ 2 ≤ (2 * (L : ℝ) + 1) ^ d :=
    (mul_le_mul_iff_right₀ (pow_pos hn0 (2 * d))).mp hproduct
  have hnlargeReal : (2 * (L : ℝ) + 1) ^ d < (n : ℝ) := by exact_mod_cast hnlarge
  nlinarith [mul_nonneg hn0.le (show 0 ≤ (n : ℝ) - 1 by linarith)]

#print axioms isolatedMassImpossible

-- End complete component: Final.lean





set_option autoImplicit false
open MME
namespace RawBudgetBridge

noncomputable local instance rawBridgeDecidableEq (N L G : ℕ) :
    DecidableEq (CWQ6ExactCoupledAddress N L G) := Classical.decEq _

-- Complete accepted source by marwahaha; submission 0ef0b27b-b298-407f-a931-df0f219c35cd.



/-- The collision-free core is isolated even against all discarded edges,
not merely injective internally.  This is the property needed to turn common
hash buckets into an induced retained family. -/
theorem mme_finset_prune_two_mode_collisions_isolated
    {α β γ : Type} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (E : Finset α) (x : α → β) (y : α → γ) :
    ∃ F : Finset α,
      F ⊆ E ∧
      (∀ e ∈ F, ∀ e' ∈ E,
        x e = x e' ∨ y e = y e' → e = e') ∧
      E.card ≤ F.card +
        ((E.product E).filter (fun p =>
          p.1 ≠ p.2 ∧ (x p.1 = x p.2 ∨ y p.1 = y p.2))).card := by
  classical
  let collisionPairs : Finset (α × α) :=
    (E.product E).filter (fun p =>
      p.1 ≠ p.2 ∧ (x p.1 = x p.2 ∨ y p.1 = y p.2))
  let F : Finset α := E.filter (fun e =>
    ∀ e' ∈ E, e ≠ e' → x e ≠ x e' ∧ y e ≠ y e')
  have hFE : F ⊆ E := by
    intro e he
    exact (Finset.mem_filter.mp he).1
  have hisolated : ∀ e ∈ F, ∀ e' ∈ E,
      x e = x e' ∨ y e = y e' → e = e' := by
    intro e he e' he'E hcollision
    by_contra hne
    have hsep := (Finset.mem_filter.mp he).2 e' he'E hne
    exact hcollision.elim hsep.1 hsep.2
  have hbadExists (e : ↥(E \ F)) :
      ∃ e' : α, e' ∈ E ∧ e.1 ≠ e' ∧
        (x e.1 = x e' ∨ y e.1 = y e') := by
    have heEF := Finset.mem_sdiff.mp e.2
    have henot : ¬ ∀ e' ∈ E, e.1 ≠ e' →
        x e.1 ≠ x e' ∧ y e.1 ≠ y e' := by
      intro h
      exact heEF.2 (Finset.mem_filter.mpr ⟨heEF.1, h⟩)
    push_neg at henot
    obtain ⟨e', he'E, hne, hcollision⟩ := henot
    exact ⟨e', he'E, hne, by tauto⟩
  let other (e : ↥(E \ F)) : α := Classical.choose (hbadExists e)
  have hother (e : ↥(E \ F)) :
      other e ∈ E ∧ e.1 ≠ other e ∧
        (x e.1 = x (other e) ∨ y e.1 = y (other e)) :=
    Classical.choose_spec (hbadExists e)
  let toCollision (e : ↥(E \ F)) : ↥collisionPairs :=
    ⟨(e.1, other e), by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨(Finset.mem_sdiff.mp e.2).1,
        (hother e).1⟩, ?_⟩
      exact ⟨(hother e).2.1, (hother e).2.2⟩⟩
  have htoCollision : Function.Injective toCollision := by
    intro e f hef
    apply Subtype.ext
    exact congrArg Prod.fst (congrArg Subtype.val hef)
  have hbadCard : (E \ F).card ≤ collisionPairs.card := by
    rw [← Fintype.card_coe, ← Fintype.card_coe]
    exact Fintype.card_le_of_injective toCollision htoCollision
  refine ⟨F, hFE, hisolated, ?_⟩
  change E.card ≤ F.card + collisionPairs.card
  have hsplit := Finset.card_sdiff_add_card_eq_card hFE
  omega


-- The previous sketch's dependency on Open raw is replaced by an explicit hypothesis.
theorem raw_implies_isolated (raw : ∃ d : ℕ, 0 < d ∧
      ∀ (N L G : ℕ),
        CWQ6ExactAddressRegularity N L G →
        (0 < L ∧ L + G = N ∧ 341 * L < 100 * G) →
        let Zcount : ℕ :=
          Nat.choose (2 * N) L * Nat.choose (2 * N - L) L
        let Xcount : ℕ := Nat.choose N G
        let middle : ℕ := Nat.choose (2 * G) G
        let Mmod : ℕ := 4 * Xcount ^ 2 + 1
        ∀ S : Finset ℕ,
          S ⊆ Finset.range (Mmod / 2) →
          ThreeAPFree (S : Set ℕ) →
          0 < S.card →
          ∃ E : Finset (CWQ6ExactCoupledAddress N L G),
            ∃ H : ℕ,
              0 < H ∧
              (E.image (fun e => e.1 2)).card ≤ Zcount ∧
              (∀ c ∈ E.image (fun e => e.1 2),
                (E.filter (fun e => e.1 2 = c)).card ≤ middle) ∧
              (∀ ex ∈ E, ∀ ey ∈ E, ∀ ez ∈ E,
                CWQ6CoupledCoordinatewiseSupported
                    (cwQ6CoupledMixedAddress ex.1 ey.1 ez.1) →
                  ∃ e' ∈ E,
                    e'.1 0 = ex.1 0 ∧
                    e'.1 1 = ey.1 1 ∧
                    e'.1 2 = ez.1 2) ∧
              H ≤ 4 ^ N ∧
              (middle : ℝ) *
                  ((((S.card : ℝ) / (Mmod : ℝ)) ^ d) /
                    (((N + 1 : ℕ) : ℝ) ^ d)) ≤
                4 * (Xcount : ℝ) ^ 2 * (H : ℝ) ∧
              (H : ℝ) * (Zcount : ℝ) +
                    (middle : ℝ) *
                      ((Zcount : ℝ) *
                        ((((S.card : ℝ) / (Mmod : ℝ)) ^ d) /
                          (((N + 1 : ℕ) : ℝ) ^ d))) +
                    (((E.product E).filter (fun p =>
                      p.1 ≠ p.2 ∧
                        (p.1.1 0 = p.2.1 0 ∨
                          p.1.1 1 = p.2.1 1))).card : ℝ) ≤
                (E.card : ℝ)) :
    ∃ d : ℕ, 0 < d ∧
      ∀ (N L G : ℕ),
        CWQ6ExactAddressRegularity N L G →
        (0 < L ∧ L + G = N ∧ 341 * L < 100 * G) →
        let Zcount : ℕ :=
          Nat.choose (2 * N) L * Nat.choose (2 * N - L) L
        let Xcount : ℕ := Nat.choose N G
        let middle : ℕ := Nat.choose (2 * G) G
        let Mmod : ℕ := 4 * Xcount ^ 2 + 1
        ∀ S : Finset ℕ,
          S ⊆ Finset.range (Mmod / 2) →
          ThreeAPFree (S : Set ℕ) →
          0 < S.card →
          ∃ E I : Finset (CWQ6ExactCoupledAddress N L G),
            ∃ H : ℕ,
              0 < H ∧
              I ⊆ E ∧
              (∀ e ∈ I, ∀ e' ∈ E,
                (e.1 0 = e'.1 0 ∨ e.1 1 = e'.1 1) → e = e') ∧
              (∀ c ∈ I.image (fun e => e.1 2),
                (I.filter (fun e => e.1 2 = c)).card ≤ middle) ∧
              (∀ ex ∈ I, ∀ ey ∈ I, ∀ ez ∈ I,
                CWQ6CoupledCoordinatewiseSupported
                    (cwQ6CoupledMixedAddress ex.1 ey.1 ez.1) →
                  ∃ e' ∈ E,
                    e'.1 0 = ex.1 0 ∧
                    e'.1 1 = ey.1 1 ∧
                    e'.1 2 = ez.1 2) ∧
              H ≤ 4 ^ N ∧
              (middle : ℝ) *
                  ((((S.card : ℝ) / (Mmod : ℝ)) ^ d) /
                    (((N + 1 : ℕ) : ℝ) ^ d)) ≤
                4 * (Xcount : ℝ) ^ 2 * (H : ℝ) ∧
              (H : ℝ) *
                    ((I.image (fun e => e.1 2)).card : ℝ) +
                  (middle : ℝ) *
                    ((Zcount : ℝ) *
                      ((((S.card : ℝ) / (Mmod : ℝ)) ^ d) /
                        (((N + 1 : ℕ) : ℝ) ^ d))) ≤
                (I.card : ℝ) := by
  classical
  obtain ⟨d, hd, hraw⟩ :=
    raw
  refine ⟨d, hd, ?_⟩
  intro N L G hregular hprofile
  dsimp only
  intro S hSrange hSfree hSpos
  obtain ⟨E, H, hH, himageE, hmaxE, hclosedE,
      hHupper, hmiddle, hmassE⟩ :=
    hraw N L G hregular hprofile S hSrange hSfree hSpos
  obtain ⟨I, hIE, hisolated, hprune⟩ :=
    mme_finset_prune_two_mode_collisions_isolated
      E (fun e => e.1 0) (fun e => e.1 1)
  have himageIE : I.image (fun e => e.1 2) ⊆
      E.image (fun e => e.1 2) := by
    intro c hc
    obtain ⟨e, heI, rfl⟩ := Finset.mem_image.mp hc
    exact Finset.mem_image_of_mem _ (hIE heI)
  have himageI : (I.image (fun e => e.1 2)).card ≤
      Nat.choose (2 * N) L * Nat.choose (2 * N - L) L :=
    (Finset.card_le_card himageIE).trans himageE
  have hmaxI : ∀ c ∈ I.image (fun e => e.1 2),
      (I.filter (fun e => e.1 2 = c)).card ≤ Nat.choose (2 * G) G := by
    intro c hc
    have hcE := himageIE hc
    have hfiber : I.filter (fun e => e.1 2 = c) ⊆
        E.filter (fun e => e.1 2 = c) := by
      intro e he
      exact Finset.mem_filter.mpr
        ⟨hIE (Finset.mem_filter.mp he).1, (Finset.mem_filter.mp he).2⟩
    exact (Finset.card_le_card hfiber).trans (hmaxE c hcE)
  have hclosedI : ∀ ex ∈ I, ∀ ey ∈ I, ∀ ez ∈ I,
      CWQ6CoupledCoordinatewiseSupported
          (cwQ6CoupledMixedAddress ex.1 ey.1 ez.1) →
        ∃ e' ∈ E,
          e'.1 0 = ex.1 0 ∧
          e'.1 1 = ey.1 1 ∧
          e'.1 2 = ez.1 2 := by
    intro ex hex ey hey ez hez hsupp
    exact hclosedE ex (hIE hex) ey (hIE hey) ez (hIE hez) hsupp
  let C : Finset
      (CWQ6ExactCoupledAddress N L G × CWQ6ExactCoupledAddress N L G) :=
    (E.product E).filter (fun p =>
      p.1 ≠ p.2 ∧
        (p.1.1 0 = p.2.1 0 ∨ p.1.1 1 = p.2.1 1))
  have hpruneR : (E.card : ℝ) ≤ (I.card : ℝ) + (C.card : ℝ) := by
    exact_mod_cast hprune
  have hmassWithC := hmassE.trans hpruneR
  have hmassNoC :
      (H : ℝ) *
            (Nat.choose (2 * N) L *
              Nat.choose (2 * N - L) L : ℕ) +
          (Nat.choose (2 * G) G : ℝ) *
            (((Nat.choose (2 * N) L *
                Nat.choose (2 * N - L) L : ℕ) : ℝ) *
              ((((S.card : ℝ) /
                  (4 * (Nat.choose N G) ^ 2 + 1 : ℕ)) ^ d) /
                (((N + 1 : ℕ) : ℝ) ^ d))) ≤
        (I.card : ℝ) := by
    exact (add_le_add_iff_right (C.card : ℝ)).mp hmassWithC
  have hfirst :
      (H : ℝ) * ((I.image (fun e => e.1 2)).card : ℝ) ≤
        (H : ℝ) *
          ((Nat.choose (2 * N) L *
            Nat.choose (2 * N - L) L : ℕ) : ℝ) := by
    apply mul_le_mul_of_nonneg_left
    · exact_mod_cast himageI
    · positivity
  have hmassI :
      (H : ℝ) * ((I.image (fun e => e.1 2)).card : ℝ) +
          (Nat.choose (2 * G) G : ℝ) *
            (((Nat.choose (2 * N) L *
                Nat.choose (2 * N - L) L : ℕ) : ℝ) *
              ((((S.card : ℝ) /
                  (4 * (Nat.choose N G) ^ 2 + 1 : ℕ)) ^ d) /
                (((N + 1 : ℕ) : ℝ) ^ d))) ≤
        (I.card : ℝ) :=
    (add_le_add hfirst (le_refl _)).trans hmassNoC
  exact ⟨E, I, H, hH, hIE, hisolated, hmaxI, hclosedI,
    hHupper, hmiddle, hmassI⟩


end RawBudgetBridge

#print axioms RawBudgetBridge.raw_implies_isolated

noncomputable local instance rawDisproofDecidableEq (N L G : ℕ) :
    DecidableEq (CWQ6ExactCoupledAddress N L G) := Classical.decEq _

theorem rawBudgetImpossible : ¬ (∃ d : ℕ, 0 < d ∧
      ∀ (N L G : ℕ),
        CWQ6ExactAddressRegularity N L G →
        (0 < L ∧ L + G = N ∧ 341 * L < 100 * G) →
        let Zcount : ℕ :=
          Nat.choose (2 * N) L * Nat.choose (2 * N - L) L
        let Xcount : ℕ := Nat.choose N G
        let middle : ℕ := Nat.choose (2 * G) G
        let Mmod : ℕ := 4 * Xcount ^ 2 + 1
        ∀ S : Finset ℕ,
          S ⊆ Finset.range (Mmod / 2) →
          ThreeAPFree (S : Set ℕ) →
          0 < S.card →
          ∃ E : Finset (CWQ6ExactCoupledAddress N L G),
            ∃ H : ℕ,
              0 < H ∧
              (E.image (fun e => e.1 2)).card ≤ Zcount ∧
              (∀ c ∈ E.image (fun e => e.1 2),
                (E.filter (fun e => e.1 2 = c)).card ≤ middle) ∧
              (∀ ex ∈ E, ∀ ey ∈ E, ∀ ez ∈ E,
                CWQ6CoupledCoordinatewiseSupported
                    (cwQ6CoupledMixedAddress ex.1 ey.1 ez.1) →
                  ∃ e' ∈ E,
                    e'.1 0 = ex.1 0 ∧
                    e'.1 1 = ey.1 1 ∧
                    e'.1 2 = ez.1 2) ∧
              H ≤ 4 ^ N ∧
              (middle : ℝ) *
                  ((((S.card : ℝ) / (Mmod : ℝ)) ^ d) /
                    (((N + 1 : ℕ) : ℝ) ^ d)) ≤
                4 * (Xcount : ℝ) ^ 2 * (H : ℝ) ∧
              (H : ℝ) * (Zcount : ℝ) +
                    (middle : ℝ) *
                      ((Zcount : ℝ) *
                        ((((S.card : ℝ) / (Mmod : ℝ)) ^ d) /
                          (((N + 1 : ℕ) : ℝ) ^ d))) +
                    (((E.product E).filter (fun p =>
                      p.1 ≠ p.2 ∧
                        (p.1.1 0 = p.2.1 0 ∨
                          p.1.1 1 = p.2.1 1))).card : ℝ) ≤
                (E.card : ℝ)) := by
  intro hraw
  exact isolatedMassImpossible (RawBudgetBridge.raw_implies_isolated hraw)

#print axioms rawBudgetImpossible










set_option autoImplicit false
open MME
namespace BucketBudgetBridge

noncomputable local instance bucketBridgeDecidableEq (N L G : ℕ) :
    DecidableEq (CWQ6ExactCoupledAddress N L G) := Classical.decEq _

-- Complete ACCEPTED source by marwahaha; submission 5567385e-2b82-41da-9df4-92271d1212d8.



open MME BigOperators

theorem mme_CW_q6_doubled_hash_AP_identity
    {R : Type} [CommSemiring R] {N : ℕ}
    (b0 : R) (w : Fin (2 * N) → R)
    (x y z : CWQ6CoupledAddress N)
    (hsupp : CWQ6CoupledCoordinatewiseSupported
      (cwQ6CoupledMixedAddress x y z)) :
    cwQ6DoubledXHash b0 w (x 0) +
        cwQ6DoubledYHash b0 w (y 1) =
      2 * cwQ6DoubledZHash b0 w (z 2) := by
  simp only [cwQ6DoubledXHash, cwQ6DoubledYHash,
    cwQ6DoubledZHash]
  ring_nf
  rw [Finset.sum_mul]
  rw [add_assoc]
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  specialize hsupp j
  change
    (x 0 j = 0 ∧ y 1 j = 0 ∧ z 2 j = 0) ∨
    (x 0 j = 1 ∧ y 1 j = 1 ∧ z 2 j = 1) ∨
    (x 0 j = 0 ∧ y 1 j = 1 ∧ z 2 j = 2) ∨
    (x 0 j = 1 ∧ y 1 j = 0 ∧ z 2 j = 2) at hsupp
  rcases hsupp with h | h | h | h
  all_goals
    rcases h with ⟨hx, hy, hz⟩
    simp [hx, hy, hz, cwQ6CoupledZHashCode] <;> ring

-- Complete ACCEPTED source by Shuze Chen; submission 5ac70b60-5403-49fd-8391-f146468cfc8a.


theorem mme_3AP_free_no_collision {n : ℕ}
    (S : Finset ℕ) (hS : ThreeAPFree (S : Set ℕ))
    (I J K : Fin n → ℕ)
    (hI : ∀ i, I i ∈ S) (hJ : ∀ i, J i ∈ S) (hK : ∀ i, K i ∈ S)
    (h : ∀ i, I i + K i = 2 * J i) :
    I = K := by
  funext i
  have hIi : I i ∈ (S : Set ℕ) := hI i
  have hJi : J i ∈ (S : Set ℕ) := hJ i
  have hKi : K i ∈ (S : Set ℕ) := hK i
  have hi := h i
  have heq : I i + K i = J i + J i := by omega
  have h1 : I i = J i := hS hIi hJi hKi heq
  omega

-- Complete ACCEPTED source by marwahaha; submission e2d72126-1c68-490f-bf30-ca839b07c134.



theorem mme_threeAP_free_half_modulus_no_collision
    (M : ℕ) (S : Finset ℕ)
    (hSrange : S ⊆ Finset.range (M / 2))
    (hSfree : ThreeAPFree (S : Set ℕ))
    (a b c : ℕ) (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hmod : (a : ZMod M) + (c : ZMod M) = 2 * (b : ZMod M)) :
    a = b ∧ b = c := by
  have haM : a < M / 2 := Finset.mem_range.mp (hSrange ha)
  have hbM : b < M / 2 := Finset.mem_range.mp (hSrange hb)
  have hcM : c < M / 2 := Finset.mem_range.mp (hSrange hc)
  have hacM : a + c < M := by omega
  have htwobM : 2 * b < M := by omega
  have hnat : a + c = 2 * b := by
    have hcast : ((a + c : ℕ) : ZMod M) = ((2 * b : ℕ) : ZMod M) := by
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hmod
    exact (ZMod.natCast_eq_natCast_iff (a + c) (2 * b) M).mp hcast
      |>.eq_of_lt_of_lt hacM htwobM
  have hfun := mme_3AP_free_no_collision S hSfree
    (fun _ : Fin 1 => a) (fun _ : Fin 1 => b) (fun _ : Fin 1 => c)
    (fun _ => ha) (fun _ => hb) (fun _ => hc) (fun _ => hnat)
  have hac : a = c := congrFun hfun 0
  constructor <;> omega

-- Complete ACCEPTED source by marwahaha; submission 95d2e7ef-4bcd-4758-aa07-f61a4476c18d.




open MME

/-- Retained lower-half Salem--Spencer labels of a supported mixed address
must agree.  Doubling is cancellable because the CW modulus is odd. -/
theorem mme_CW_q6_hash_bucket_coherence
    (N Xcount : ℕ)
    (S : Finset ℕ)
    (hSrange : S ⊆ Finset.range ((4 * Xcount ^ 2 + 1) / 2))
    (hSfree : ThreeAPFree (S : Set ℕ))
    (b0 : ZMod (4 * Xcount ^ 2 + 1))
    (w : Fin (2 * N) → ZMod (4 * Xcount ^ 2 + 1))
    (x y z : CWQ6CoupledAddress N)
    (hsupp : CWQ6CoupledCoordinatewiseSupported
      (cwQ6CoupledMixedAddress x y z))
    (sx sy sz : ℕ) (hsx : sx ∈ S) (hsy : sy ∈ S) (hsz : sz ∈ S)
    (hx : cwQ6DoubledXHash b0 w (x 0) =
      2 * (sx : ZMod (4 * Xcount ^ 2 + 1)))
    (hy : cwQ6DoubledYHash b0 w (y 1) =
      2 * (sy : ZMod (4 * Xcount ^ 2 + 1)))
    (hz : cwQ6DoubledZHash b0 w (z 2) =
      2 * (sz : ZMod (4 * Xcount ^ 2 + 1))) :
    sx = sy ∧ sy = sz := by
  let Mmod : ℕ := 4 * Xcount ^ 2 + 1
  have hhash := mme_CW_q6_doubled_hash_AP_identity b0 w x y z hsupp
  rw [hx, hy, hz] at hhash
  have hodd : Odd Mmod := by
    refine ⟨2 * Xcount ^ 2, ?_⟩
    dsimp [Mmod]
    omega
  have htwoUnit : IsUnit (2 : ZMod Mmod) := by
    change IsUnit ((2 : ℕ) : ZMod Mmod)
    rw [ZMod.isUnit_iff_coprime]
    exact hodd.coprime_two_left
  have hmod : (sx : ZMod Mmod) + (sy : ZMod Mmod) =
      2 * (sz : ZMod Mmod) := by
    apply htwoUnit.mul_left_cancel
    simpa [mul_add, mul_assoc] using hhash
  have hcollision := mme_threeAP_free_half_modulus_no_collision
    Mmod S (by simpa [Mmod] using hSrange) hSfree sx sz sy hsx hsz hsy hmod
  exact ⟨hcollision.1.trans hcollision.2, hcollision.2.symm⟩

-- Complete ACCEPTED source by marwahaha; submission be09b7d2-c2ba-4053-8fd3-0c241e79028e.



open MME

/-- The literal retained hash bucket has the expected Z-count and degree
upper bounds and is closed under every supported retained mode mix. -/
theorem mme_CW_q6_primary_hash_bucket_structure
    (N L G Xcount : ℕ)
    (hregular : CWQ6ExactAddressRegularity N L G)
    (S : Finset ℕ)
    (hSrange : S ⊆ Finset.range ((4 * Xcount ^ 2 + 1) / 2))
    (hSfree : ThreeAPFree (S : Set ℕ))
    (b0 : ZMod (4 * Xcount ^ 2 + 1))
    (w : Fin (2 * N) → ZMod (4 * Xcount ^ 2 + 1)) :
    let E := cwQ6PrimaryHashBucket N L G Xcount S b0 w
    (E.image (fun e => e.1 2)).card ≤
        Nat.choose (2 * N) L * Nat.choose (2 * N - L) L ∧
    (∀ c ∈ E.image (fun e => e.1 2),
      (E.filter (fun e => e.1 2 = c)).card ≤ Nat.choose (2 * G) G) ∧
    ∀ ex ∈ E, ∀ ey ∈ E, ∀ ez ∈ E,
      CWQ6CoupledCoordinatewiseSupported
          (cwQ6CoupledMixedAddress ex.1 ey.1 ez.1) →
        ∃ e' ∈ E,
          e'.1 0 = ex.1 0 ∧
          e'.1 1 = ey.1 1 ∧
          e'.1 2 = ez.1 2 := by
  classical
  let E := cwQ6PrimaryHashBucket N L G Xcount S b0 w
  have hrawMem (e : CWQ6ExactCoupledAddress N L G) :
      e.1 ∈ cwQ6ExactAddresses N L G := by
    simp only [cwQ6ExactAddresses, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact e.2
  have hzImage : E.image (fun e => e.1 2) ⊆ cwQ6ExactZWords N L G := by
    intro c hc
    obtain ⟨e, heE, rfl⟩ := Finset.mem_image.mp hc
    exact Finset.mem_image.mpr ⟨e.1, hrawMem e, rfl⟩
  have himageCard : (E.image (fun e => e.1 2)).card ≤
      Nat.choose (2 * N) L * Nat.choose (2 * N - L) L := by
    exact (Finset.card_le_card hzImage).trans_eq hregular.z_word_card
  refine ⟨himageCard, ?_, ?_⟩
  · intro c hc
    have hcZ : c ∈ cwQ6ExactZWords N L G := hzImage hc
    let fiberImage : Finset (CWQ6CoupledAddress N) :=
      (E.filter (fun e => e.1 2 = c)).image (fun e => e.1)
    have hcardEq : fiberImage.card =
        (E.filter (fun e => e.1 2 = c)).card := by
      exact Finset.card_image_of_injective _ Subtype.val_injective
    have hfiberSubset : fiberImage ⊆
        (cwQ6ExactAddresses N L G).filter (fun e => e 2 = c) := by
      intro a ha
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ha
      exact Finset.mem_filter.mpr
        ⟨hrawMem e, (Finset.mem_filter.mp he).2⟩
    rw [← hcardEq]
    exact (Finset.card_le_card hfiberSubset).trans_eq
      (hregular.z_degree c hcZ)
  · intro ex hex ey hey ez hez hsupp
    have hex' : ∃ s ∈ S,
        cwQ6DoubledXHash b0 w (ex.1 0) =
            2 * (s : ZMod (4 * Xcount ^ 2 + 1)) ∧
        cwQ6DoubledYHash b0 w (ex.1 1) =
            2 * (s : ZMod (4 * Xcount ^ 2 + 1)) ∧
        cwQ6DoubledZHash b0 w (ex.1 2) =
            2 * (s : ZMod (4 * Xcount ^ 2 + 1)) := by
      simpa only [E, cwQ6PrimaryHashBucket, Finset.mem_filter,
        Finset.mem_univ, true_and] using hex
    have hey' : ∃ s ∈ S,
        cwQ6DoubledXHash b0 w (ey.1 0) =
            2 * (s : ZMod (4 * Xcount ^ 2 + 1)) ∧
        cwQ6DoubledYHash b0 w (ey.1 1) =
            2 * (s : ZMod (4 * Xcount ^ 2 + 1)) ∧
        cwQ6DoubledZHash b0 w (ey.1 2) =
            2 * (s : ZMod (4 * Xcount ^ 2 + 1)) := by
      simpa only [E, cwQ6PrimaryHashBucket, Finset.mem_filter,
        Finset.mem_univ, true_and] using hey
    have hez' : ∃ s ∈ S,
        cwQ6DoubledXHash b0 w (ez.1 0) =
            2 * (s : ZMod (4 * Xcount ^ 2 + 1)) ∧
        cwQ6DoubledYHash b0 w (ez.1 1) =
            2 * (s : ZMod (4 * Xcount ^ 2 + 1)) ∧
        cwQ6DoubledZHash b0 w (ez.1 2) =
            2 * (s : ZMod (4 * Xcount ^ 2 + 1)) := by
      simpa only [E, cwQ6PrimaryHashBucket, Finset.mem_filter,
        Finset.mem_univ, true_and] using hez
    obtain ⟨sx, hsx, hxx, _hxy, _hxz⟩ := hex'
    obtain ⟨sy, hsy, _hyx, hyy, _hyz⟩ := hey'
    obtain ⟨sz, hsz, _hzx, _hzy, hzz⟩ := hez'
    have hcoherent := mme_CW_q6_hash_bucket_coherence
      N Xcount S hSrange hSfree b0 w ex.1 ey.1 ez.1 hsupp
      sx sy sz hsx hsy hsz hxx hyy hzz
    let a : CWQ6CoupledAddress N :=
      cwQ6CoupledMixedAddress ex.1 ey.1 ez.1
    have haExact :
        CWQ6CoupledCoordinatewiseSupported a ∧
          ∀ i r : Fin 3,
            (Finset.univ.filter (fun j : Fin (2 * N) => a i j = r)).card =
              cwQ6CoupledMarginalMultiplicity N L G i r := by
      refine ⟨hsupp, ?_⟩
      intro i r
      fin_cases i
      · exact ex.2.2 (0 : Fin 3) r
      · exact ey.2.2 (1 : Fin 3) r
      · exact ez.2.2 (2 : Fin 3) r
    let e' : CWQ6ExactCoupledAddress N L G := ⟨a, haExact⟩
    have he'E : e' ∈ E := by
      change e' ∈ cwQ6PrimaryHashBucket N L G Xcount S b0 w
      simp only [cwQ6PrimaryHashBucket, Finset.mem_filter,
        Finset.mem_univ, true_and]
      refine ⟨sx, hsx, ?_, ?_, ?_⟩
      · simpa [e', a, cwQ6CoupledMixedAddress] using hxx
      · simpa [e', a, cwQ6CoupledMixedAddress, hcoherent.1] using hyy
      · simpa [e', a, cwQ6CoupledMixedAddress,
          hcoherent.1, hcoherent.2] using hzz
    refine ⟨e', he'E, ?_, ?_, ?_⟩ <;>
      rfl


-- Adapted from marwahaha's conditional sketch d6ac0404-96b0-4e27-800e-03a011e027a9.
-- Its Open child is an explicit hypothesis here; the entire remaining body is unchanged.
theorem averaging_implies_raw (averaging : ∃ d : ℕ, 0 < d ∧
      ∀ (N L G : ℕ),
        CWQ6ExactAddressRegularity N L G →
        (0 < L ∧ L + G = N ∧ 341 * L < 100 * G) →
        let Zcount : ℕ :=
          Nat.choose (2 * N) L * Nat.choose (2 * N - L) L
        let Xcount : ℕ := Nat.choose N G
        let middle : ℕ := Nat.choose (2 * G) G
        let Mmod : ℕ := 4 * Xcount ^ 2 + 1
        ∀ S : Finset ℕ,
          S ⊆ Finset.range (Mmod / 2) →
          ThreeAPFree (S : Set ℕ) →
          0 < S.card →
          ∃ b0 : ZMod Mmod,
            ∃ w : Fin (2 * N) → ZMod Mmod,
              ∃ H : ℕ,
                let E := cwQ6PrimaryHashBucket N L G Xcount S b0 w
                0 < H ∧
                H ≤ 4 ^ N ∧
                (middle : ℝ) *
                    ((((S.card : ℝ) / (Mmod : ℝ)) ^ d) /
                      (((N + 1 : ℕ) : ℝ) ^ d)) ≤
                  4 * (Xcount : ℝ) ^ 2 * (H : ℝ) ∧
                (H : ℝ) * (Zcount : ℝ) +
                      (middle : ℝ) *
                        ((Zcount : ℝ) *
                          ((((S.card : ℝ) / (Mmod : ℝ)) ^ d) /
                            (((N + 1 : ℕ) : ℝ) ^ d))) +
                      (((E.product E).filter (fun p =>
                        p.1 ≠ p.2 ∧
                          (p.1.1 0 = p.2.1 0 ∨
                            p.1.1 1 = p.2.1 1))).card : ℝ) ≤
                  (E.card : ℝ)) :
    ∃ d : ℕ, 0 < d ∧
      ∀ (N L G : ℕ),
        CWQ6ExactAddressRegularity N L G →
        (0 < L ∧ L + G = N ∧ 341 * L < 100 * G) →
        let Zcount : ℕ :=
          Nat.choose (2 * N) L * Nat.choose (2 * N - L) L
        let Xcount : ℕ := Nat.choose N G
        let middle : ℕ := Nat.choose (2 * G) G
        let Mmod : ℕ := 4 * Xcount ^ 2 + 1
        ∀ S : Finset ℕ,
          S ⊆ Finset.range (Mmod / 2) →
          ThreeAPFree (S : Set ℕ) →
          0 < S.card →
          ∃ E : Finset (CWQ6ExactCoupledAddress N L G),
            ∃ H : ℕ,
              0 < H ∧
              (E.image (fun e => e.1 2)).card ≤ Zcount ∧
              (∀ c ∈ E.image (fun e => e.1 2),
                (E.filter (fun e => e.1 2 = c)).card ≤ middle) ∧
              (∀ ex ∈ E, ∀ ey ∈ E, ∀ ez ∈ E,
                CWQ6CoupledCoordinatewiseSupported
                    (cwQ6CoupledMixedAddress ex.1 ey.1 ez.1) →
                  ∃ e' ∈ E,
                    e'.1 0 = ex.1 0 ∧
                    e'.1 1 = ey.1 1 ∧
                    e'.1 2 = ez.1 2) ∧
              H ≤ 4 ^ N ∧
              (middle : ℝ) *
                  ((((S.card : ℝ) / (Mmod : ℝ)) ^ d) /
                    (((N + 1 : ℕ) : ℝ) ^ d)) ≤
                4 * (Xcount : ℝ) ^ 2 * (H : ℝ) ∧
              (H : ℝ) * (Zcount : ℝ) +
                    (middle : ℝ) *
                      ((Zcount : ℝ) *
                        ((((S.card : ℝ) / (Mmod : ℝ)) ^ d) /
                          (((N + 1 : ℕ) : ℝ) ^ d))) +
                    (((E.product E).filter (fun p =>
                      p.1 ≠ p.2 ∧
                        (p.1.1 0 = p.2.1 0 ∨
                          p.1.1 1 = p.2.1 1))).card : ℝ) ≤
                (E.card : ℝ) := by
  obtain ⟨d, hd, havg⟩ :=
    averaging
  refine ⟨d, hd, ?_⟩
  intro N L G hregular hprofile
  dsimp only
  intro S hSrange hSfree hSpos
  obtain ⟨b0, w, H, hH, hHupper, hmiddle, hmass⟩ :=
    havg N L G hregular hprofile S hSrange hSfree hSpos
  let E := cwQ6PrimaryHashBucket N L G (Nat.choose N G) S b0 w
  have hstruct := mme_CW_q6_primary_hash_bucket_structure
    N L G (Nat.choose N G) hregular S hSrange hSfree b0 w
  dsimp only at hstruct
  exact ⟨E, H, hH, hstruct.1, hstruct.2.1, hstruct.2.2,
    hHupper, hmiddle, hmass⟩


end BucketBudgetBridge

#print axioms BucketBudgetBridge.averaging_implies_raw

noncomputable local instance averagingDisproofDecidableEq (N L G : ℕ) :
    DecidableEq (CWQ6ExactCoupledAddress N L G) := Classical.decEq _

theorem solution : ¬ (∃ d : ℕ, 0 < d ∧
      ∀ (N L G : ℕ),
        CWQ6ExactAddressRegularity N L G →
        (0 < L ∧ L + G = N ∧ 341 * L < 100 * G) →
        let Zcount : ℕ :=
          Nat.choose (2 * N) L * Nat.choose (2 * N - L) L
        let Xcount : ℕ := Nat.choose N G
        let middle : ℕ := Nat.choose (2 * G) G
        let Mmod : ℕ := 4 * Xcount ^ 2 + 1
        ∀ S : Finset ℕ,
          S ⊆ Finset.range (Mmod / 2) →
          ThreeAPFree (S : Set ℕ) →
          0 < S.card →
          ∃ b0 : ZMod Mmod,
            ∃ w : Fin (2 * N) → ZMod Mmod,
              ∃ H : ℕ,
                let E := cwQ6PrimaryHashBucket N L G Xcount S b0 w
                0 < H ∧
                H ≤ 4 ^ N ∧
                (middle : ℝ) *
                    ((((S.card : ℝ) / (Mmod : ℝ)) ^ d) /
                      (((N + 1 : ℕ) : ℝ) ^ d)) ≤
                  4 * (Xcount : ℝ) ^ 2 * (H : ℝ) ∧
                (H : ℝ) * (Zcount : ℝ) +
                      (middle : ℝ) *
                        ((Zcount : ℝ) *
                          ((((S.card : ℝ) / (Mmod : ℝ)) ^ d) /
                            (((N + 1 : ℕ) : ℝ) ^ d))) +
                      (((E.product E).filter (fun p =>
                        p.1 ≠ p.2 ∧
                          (p.1.1 0 = p.2.1 0 ∨
                            p.1.1 1 = p.2.1 1))).card : ℝ) ≤
                  (E.card : ℝ)) := by
  intro havg
  exact rawBudgetImpossible (BucketBudgetBridge.averaging_implies_raw havg)

#print axioms solution
