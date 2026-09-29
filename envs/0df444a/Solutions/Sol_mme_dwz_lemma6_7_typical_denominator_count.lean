-- Prove2me | solution 1 for mme_dwz_lemma6_7_typical_denominator_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T11:31:25.064133+00:00
-- url     : https://prove2.me/submissions/2b63d40e-f969-40ec-b1b7-5bc23ad9b994

import Theorems.Thm_mme_fintype_constrained_prescribed_fiber_function_card
import Mathlib

open scoped BigOperators

set_option autoImplicit false

namespace MME.DWZTypicalDenominator

/-- Multinomial coefficients factor when an alphabet is grouped into coarse
strata.  Written without division, this is the exact arithmetic identity
behind the quotient of multinomials in the denominator of DWZ Lemma 6.7. -/
theorem multinomial_grouping
    {Pair Coarse : Type*}
    [Fintype Pair] [DecidableEq Pair]
    [Fintype Coarse] [DecidableEq Coarse]
    (coarseOf : Pair → Coarse)
    (gamma : Pair → ℕ) (alphaZ : Coarse → ℕ)
    (hPush : ∀ k,
      (∑ p : {p : Pair // coarseOf p = k}, gamma p.1) = alphaZ k) :
    Nat.multinomial Finset.univ gamma =
      Nat.multinomial Finset.univ alphaZ *
        ∏ k, Nat.multinomial Finset.univ
          (fun p : {p : Pair // coarseOf p = k} => gamma p.1) := by
  classical
  let fineDen : ℕ := ∏ p : Pair, (gamma p).factorial
  let coarseDen : ℕ := ∏ k : Coarse, (alphaZ k).factorial
  let localDen : Coarse → ℕ := fun k =>
    ∏ p : {p : Pair // coarseOf p = k}, (gamma p.1).factorial
  let localMult : Coarse → ℕ := fun k =>
    Nat.multinomial Finset.univ
      (fun p : {p : Pair // coarseOf p = k} => gamma p.1)

  have hFineDen : fineDen = ∏ k : Coarse, localDen k := by
    dsimp [fineDen, localDen]
    symm
    calc
      (∏ k : Coarse, ∏ p : {p : Pair // coarseOf p = k},
          (gamma p.1).factorial) =
          ∏ x : Σ k : Coarse, {p : Pair // coarseOf p = k},
            (gamma x.2.1).factorial := by
              symm
              exact Fintype.prod_sigma _
      _ = ∏ p : Pair, (gamma p).factorial :=
        Fintype.prod_equiv (Equiv.sigmaFiberEquiv coarseOf)
          (fun x : Σ k : Coarse, {p : Pair // coarseOf p = k} =>
            (gamma x.2.1).factorial)
          (fun p : Pair => (gamma p).factorial)
          (fun _ => rfl)

  have hSum : (∑ p : Pair, gamma p) = ∑ k : Coarse, alphaZ k := by
    calc
      (∑ p : Pair, gamma p) =
          ∑ x : Σ k : Coarse, {p : Pair // coarseOf p = k}, gamma x.2.1 := by
            symm
            exact Fintype.sum_equiv (Equiv.sigmaFiberEquiv coarseOf)
              (fun x : Σ k : Coarse, {p : Pair // coarseOf p = k} => gamma x.2.1)
              gamma (fun _ => rfl)
      _ = ∑ k : Coarse, ∑ p : {p : Pair // coarseOf p = k}, gamma p.1 := by
            rw [Fintype.sum_sigma]
      _ = ∑ k : Coarse, alphaZ k := by
            apply Finset.sum_congr rfl
            intro k hk
            exact hPush k

  have hLocalSpec (k : Coarse) :
      localDen k * localMult k = (alphaZ k).factorial := by
    dsimp [localDen, localMult]
    have h := Nat.multinomial_spec
      (Finset.univ : Finset {p : Pair // coarseOf p = k})
      (fun p : {p : Pair // coarseOf p = k} => gamma p.1)
    simpa [hPush k] using h

  have hGroupedDen : fineDen * (∏ k : Coarse, localMult k) = coarseDen := by
    rw [hFineDen]
    rw [← Finset.prod_mul_distrib]
    dsimp [coarseDen]
    apply Finset.prod_congr rfl
    intro k hk
    exact hLocalSpec k

  have hFineSpec :
      fineDen * Nat.multinomial Finset.univ gamma =
        (∑ p : Pair, gamma p).factorial := by
    simpa [fineDen] using
      (Nat.multinomial_spec (Finset.univ : Finset Pair) gamma)

  have hCoarseSpec :
      coarseDen * Nat.multinomial Finset.univ alphaZ =
        (∑ k : Coarse, alphaZ k).factorial := by
    simpa [coarseDen] using
      (Nat.multinomial_spec (Finset.univ : Finset Coarse) alphaZ)

  apply Nat.eq_of_mul_eq_mul_left (m := Nat.multinomial Finset.univ gamma)
    (k := Nat.multinomial Finset.univ alphaZ * ∏ k : Coarse, localMult k)
    (n := fineDen)
  · dsimp [fineDen]
    exact Finset.prod_pos fun p hp => Nat.factorial_pos (gamma p)
  · calc
      fineDen * Nat.multinomial Finset.univ gamma =
          (∑ p : Pair, gamma p).factorial := hFineSpec
      _ = (∑ k : Coarse, alphaZ k).factorial := by rw [hSum]
      _ = coarseDen * Nat.multinomial Finset.univ alphaZ := hCoarseSpec.symm
      _ = (fineDen * ∏ k : Coarse, localMult k) *
          Nat.multinomial Finset.univ alphaZ := by rw [hGroupedDen]
      _ = fineDen *
          (Nat.multinomial Finset.univ alphaZ * ∏ k : Coarse, localMult k) := by
            ac_rfl

end MME.DWZTypicalDenominator

open MME.DWZTypicalDenominator

/-- Exact finite count of typical fine pair-words inside one fixed coarse
word.  The second conjunct is the division-free form of the quotient of
multinomials displayed immediately after Equation (23) in DWZ. -/
theorem solution
    {Position Pair Coarse : Type*}
    [Fintype Position] [DecidableEq Position]
    [Fintype Pair] [DecidableEq Pair]
    [Fintype Coarse] [DecidableEq Coarse]
    (coarseOf : Pair → Coarse) (K : Position → Coarse)
    (gamma : Pair → ℕ) (alphaZ : Coarse → ℕ)
    (hK : ∀ k,
      Fintype.card {t : Position // K t = k} = alphaZ k)
    (hPush : ∀ k,
      (∑ p : {p : Pair // coarseOf p = k}, gamma p.1) = alphaZ k) :
    let BtypicalK :=
      {small : Position → Pair //
        (∀ t, coarseOf (small t) = K t) ∧
        ∀ p, Fintype.card {t : Position // small t = p} = gamma p}
    let localCount :=
      ∏ k, Nat.multinomial Finset.univ
        (fun p : {p : Pair // coarseOf p = k} => gamma p.1)
    Nat.card BtypicalK = localCount ∧
      Nat.multinomial Finset.univ gamma =
        Nat.multinomial Finset.univ alphaZ * Nat.card BtypicalK := by
  classical
  dsimp only
  have hsize : ∀ k,
      (∑ p : {p : Pair // coarseOf p = k}, gamma p.1) =
        Fintype.card {t : Position // K t = k} := by
    intro k
    rw [hPush k, hK k]
  have hCard :=
    mme_fintype_constrained_prescribed_fiber_function_card K coarseOf gamma hsize
  have hLocal (k : Coarse) :
      (Fintype.card {t : Position // K t = k}).factorial /
          ∏ p : {p : Pair // coarseOf p = k}, (gamma p.1).factorial =
        Nat.multinomial Finset.univ
          (fun p : {p : Pair // coarseOf p = k} => gamma p.1) := by
    let denom : ℕ :=
      ∏ p : {p : Pair // coarseOf p = k}, (gamma p.1).factorial
    have hdenom : 0 < denom := by
      dsimp [denom]
      exact Finset.prod_pos fun p hp => Nat.factorial_pos (gamma p.1)
    have hspec := Nat.multinomial_spec
      (Finset.univ : Finset {p : Pair // coarseOf p = k})
      (fun p : {p : Pair // coarseOf p = k} => gamma p.1)
    have hfactorial :
        (Fintype.card {t : Position // K t = k}).factorial =
          denom * Nat.multinomial Finset.univ
            (fun p : {p : Pair // coarseOf p = k} => gamma p.1) := by
      rw [← hsize k]
      simpa [denom] using hspec.symm
    have hdiv : denom ∣ (Fintype.card {t : Position // K t = k}).factorial :=
      ⟨Nat.multinomial Finset.univ
          (fun p : {p : Pair // coarseOf p = k} => gamma p.1), hfactorial⟩
    exact (Nat.div_eq_iff_eq_mul_right hdenom hdiv).2 hfactorial
  have hExact :
      Nat.card
          {small : Position → Pair //
            (∀ t, coarseOf (small t) = K t) ∧
            ∀ p, Fintype.card {t : Position // small t = p} = gamma p} =
        ∏ k, Nat.multinomial Finset.univ
          (fun p : {p : Pair // coarseOf p = k} => gamma p.1) := by
    rw [hCard]
    apply Finset.prod_congr rfl
    intro k hk
    exact hLocal k
  refine ⟨hExact, ?_⟩
  rw [hExact]
  exact multinomial_grouping coarseOf gamma alphaZ hPush
