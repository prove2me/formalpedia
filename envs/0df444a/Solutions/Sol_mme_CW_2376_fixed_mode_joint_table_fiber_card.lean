-- Prove2me | solution 1 for mme_CW_2376_fixed_mode_joint_table_fiber_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T23:30:14.573264+00:00
-- url     : https://prove2.me/submissions/a6d4afca-3653-4bf0-9b9f-1a6f38ad8442

import Theorems.Thm_mme_fintype_constrained_prescribed_fiber_function_card
import Definitions.Def_mme_CW_2376_marginal_joint_tables

open MME BigOperators

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

private theorem card_composite_fiber
    {alpha beta iota : Type*} [Fintype alpha] [Fintype beta]
    [DecidableEq alpha] [DecidableEq beta] [DecidableEq iota]
    (g : alpha → beta) (q : beta → iota) (i : iota) :
    Fintype.card {a : alpha // q (g a) = i} =
      ∑ b : {b : beta // q b = i},
        Fintype.card {a : alpha // g a = b.1} := by
  classical
  let e : {a : alpha // q (g a) = i} ≃
      Sigma fun b : {b : beta // q b = i} =>
        {a : alpha // g a = b.1} := {
    toFun a := ⟨⟨g a.1, a.2⟩, ⟨a.1, rfl⟩⟩
    invFun a := ⟨a.2.1, by rw [a.2.2, a.1.2]⟩
    left_inv a := by
      apply Subtype.ext
      rfl
    right_inv a := by
      rcases a with ⟨⟨b, hb⟩, ⟨a, ha⟩⟩
      cases ha
      rfl
  }
  rw [Fintype.card_congr e, Fintype.card_sigma]

private theorem prod_nat_div_eq_div_prod_of_dvd
    {iota : Type*} (s : Finset iota) (A B : iota → ℕ)
    (hdiv : ∀ i ∈ s, B i ∣ A i) :
    (∏ i ∈ s, A i / B i) =
      (∏ i ∈ s, A i) / ∏ i ∈ s, B i := by
  classical
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons a s ha ih =>
      have haDiv : B a ∣ A a := hdiv a (by simp)
      have hsDiv : ∀ i ∈ s, B i ∣ A i := by
        intro i hi
        exact hdiv i (by simp [hi])
      have hprodDiv : (∏ i ∈ s, B i) ∣ ∏ i ∈ s, A i :=
        Finset.prod_dvd_prod_of_dvd _ _ hsDiv
      simp only [Finset.prod_cons]
      rw [ih hsDiv, Nat.div_mul_div_comm haDiv hprodDiv]

/-- Exact cardinality of one realized joint-table fiber in a fixed-mode
star of the full marginal-supported CW hypergraph. -/
theorem solution
    (m : ℕ) (a : CW2376MarginalSupportedAddress m) (i : Fin 3)
    (k : CW2376JointMultiplicityTable)
    (hkMarginal : ∀ l : Fin 3, ∀ r : Fin 5,
      (∑ sigma : {sigma : CW2376SupportedJointType //
          sigma.1 l = r}, k sigma.1) =
        cw2376MarginalMultiplicity m r) :
    Nat.card
        {b : CW2376MarginalSupportedAddress m //
          b.1 i = a.1 i ∧ cw2376MarginalJointTable b = k} =
      (∏ r : Fin 5, (cw2376MarginalMultiplicity m r).factorial) /
        ∏ sigma : CW2376SupportedJointType, (k sigma).factorial := by
  classical
  let Assignment :=
    {g : Fin (cw2376ProfileLength m) → CW2376SupportedJointType //
      (∀ j, (g j).1 i = a.1 i j) ∧
      ∀ sigma, Fintype.card {j // g j = sigma} = k sigma}
  let AddressClass :=
    {b : CW2376MarginalSupportedAddress m //
      b.1 i = a.1 i ∧ cw2376MarginalJointTable b = k}

  let e : AddressClass ≃ Assignment := {
    toFun b := ⟨fun j => cw2376MarginalSupportedJointTypeAt b.1 j, by
      constructor
      · intro j
        change b.1.1 i j = a.1 i j
        exact congrFun b.2.1 j
      · intro sigma
        exact congrFun b.2.2 sigma⟩
    invFun G := by
      let raw : CW2376ProfileAddress m :=
        fun l j => (G.1 j).1 l
      have hsupport : CW2376CoordinatewiseSupported raw := by
        intro j
        have hsum :=
          (mme_CW_2376_target_joint_types_iff_sum_four (G.1 j).1).1
            (G.1 j).2
        simpa only [raw] using hsum
      have hmarginal : CW2376MarginallyRegular raw := by
        intro l r
        rw [← Fintype.card_subtype]
        change Fintype.card {j : Fin (cw2376ProfileLength m) //
          (G.1 j).1 l = r} = cw2376MarginalMultiplicity m r
        rw [card_composite_fiber G.1
          (fun sigma : CW2376SupportedJointType => sigma.1 l) r]
        calc
          (∑ sigma : {sigma : CW2376SupportedJointType //
              sigma.1 l = r},
              Fintype.card {j : Fin (cw2376ProfileLength m) //
                G.1 j = sigma.1}) =
              ∑ sigma : {sigma : CW2376SupportedJointType //
                sigma.1 l = r}, k sigma.1 := by
            apply Finset.sum_congr rfl
            intro sigma hsigma
            exact G.2.2 sigma.1
          _ = cw2376MarginalMultiplicity m r := hkMarginal l r
      let b : CW2376MarginalSupportedAddress m :=
        ⟨raw, hsupport, hmarginal⟩
      refine ⟨b, ?_, ?_⟩
      · funext j
        exact G.2.1 j
      · funext sigma
        change Fintype.card
          {j : Fin (cw2376ProfileLength m) //
            cw2376MarginalSupportedJointTypeAt b j = sigma} = k sigma
        calc
          Fintype.card
              {j : Fin (cw2376ProfileLength m) //
                cw2376MarginalSupportedJointTypeAt b j = sigma} =
              Fintype.card
                {j : Fin (cw2376ProfileLength m) // G.1 j = sigma} := by
            apply Fintype.card_congr
            exact Equiv.subtypeEquiv (Equiv.refl _)
              (fun j => by
                change
                  (⟨fun l => (G.1 j).1 l, _⟩ :
                    CW2376SupportedJointType) = sigma ↔ G.1 j = sigma
                constructor
                · intro h
                  exact Subtype.ext (congrArg Subtype.val h)
                · intro h
                  exact Subtype.ext (congrArg Subtype.val h))
          _ = k sigma := G.2.2 sigma
    left_inv b := by
      apply Subtype.ext
      apply Subtype.ext
      funext l j
      rfl
    right_inv G := by
      apply Subtype.ext
      funext j
      apply Subtype.ext
      rfl
  }

  have hsum (r : Fin 5) :
      (∑ sigma : {sigma : CW2376SupportedJointType //
          sigma.1 i = r}, k sigma.1) =
        Fintype.card {j : Fin (cw2376ProfileLength m) // a.1 i j = r} := by
    rw [Fintype.card_subtype]
    exact (hkMarginal i r).trans (a.2.2 i r).symm
  have hassignment : Nat.card Assignment =
      ∏ r : Fin 5,
        (Fintype.card
          {j : Fin (cw2376ProfileLength m) // a.1 i j = r}).factorial /
          ∏ sigma : {sigma : CW2376SupportedJointType //
              sigma.1 i = r}, (k sigma.1).factorial := by
    simpa only [Assignment] using
      (mme_fintype_constrained_prescribed_fiber_function_card
        (h := a.1 i)
        (q := fun sigma : CW2376SupportedJointType => sigma.1 i)
        k hsum)
  have hrowDiv (r : Fin 5) :
      (∏ sigma : {sigma : CW2376SupportedJointType //
          sigma.1 i = r}, (k sigma.1).factorial) ∣
        (cw2376MarginalMultiplicity m r).factorial := by
    have h := Nat.prod_factorial_dvd_factorial_sum
      (Finset.univ : Finset
        {sigma : CW2376SupportedJointType // sigma.1 i = r})
      (fun sigma => k sigma.1)
    simpa [hkMarginal i r] using h
  calc
    Nat.card AddressClass = Nat.card Assignment := Nat.card_congr e
    _ = ∏ r : Fin 5,
        (Fintype.card
          {j : Fin (cw2376ProfileLength m) // a.1 i j = r}).factorial /
          ∏ sigma : {sigma : CW2376SupportedJointType //
              sigma.1 i = r}, (k sigma.1).factorial := hassignment
    _ = ∏ r : Fin 5,
        (cw2376MarginalMultiplicity m r).factorial /
          ∏ sigma : {sigma : CW2376SupportedJointType //
              sigma.1 i = r}, (k sigma.1).factorial := by
      apply Finset.prod_congr rfl
      intro r hr
      rw [Fintype.card_subtype, a.2.2 i r]
    _ = (∏ r : Fin 5,
          (cw2376MarginalMultiplicity m r).factorial) /
        ∏ r : Fin 5,
          ∏ sigma : {sigma : CW2376SupportedJointType //
            sigma.1 i = r}, (k sigma.1).factorial := by
      exact prod_nat_div_eq_div_prod_of_dvd
        (Finset.univ : Finset (Fin 5))
        (fun r => (cw2376MarginalMultiplicity m r).factorial)
        (fun r => ∏ sigma : {sigma : CW2376SupportedJointType //
          sigma.1 i = r}, (k sigma.1).factorial)
        (by
          intro r hr
          exact hrowDiv r)
    _ = (∏ r : Fin 5,
          (cw2376MarginalMultiplicity m r).factorial) /
        ∏ sigma : CW2376SupportedJointType, (k sigma).factorial := by
      congr 1
      calc
        (∏ r : Fin 5, ∏ sigma : {sigma : CW2376SupportedJointType //
            sigma.1 i = r}, (k sigma.1).factorial) =
            ∏ x : Sigma fun r : Fin 5 =>
              {sigma : CW2376SupportedJointType // sigma.1 i = r},
              (k x.2.1).factorial := by
          exact (Fintype.prod_sigma
            (fun x : Sigma fun r : Fin 5 =>
              {sigma : CW2376SupportedJointType // sigma.1 i = r} =>
              (k x.2.1).factorial)).symm
        _ = ∏ sigma : CW2376SupportedJointType,
            (k sigma).factorial := by
          exact
            (Equiv.prod_comp
              (Equiv.sigmaFiberEquiv
                (fun sigma : CW2376SupportedJointType => sigma.1 i))
              (fun sigma : CW2376SupportedJointType => (k sigma).factorial))
