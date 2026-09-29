-- Prove2me | solution 1 for mme_CW_q6_lower_bounded_isolated_address_set_to_hash_family
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T20:17:30.574482+00:00
-- url     : https://prove2.me/submissions/e3970058-fa28-4219-8d8b-f4fba2aefd54

import Theorems.Thm_mme_finset_uniform_positive_fiber_truncation
import Theorems.Thm_mme_CW_q6_uniform_isolated_address_set_to_hash_family

open MME

/-- Lower bounds on every positive Z-fiber can be truncated to a literal
common H and then enumerated as a primary q=6 hash family. -/
theorem solution
    (N L G H : ℕ)
    (E F : Finset (CWQ6ExactCoupledAddress N L G))
    (hH : 0 < H)
    (hFE : F ⊆ E)
    (hisolated : ∀ e ∈ F, ∀ e' ∈ E,
      (e.1 0 = e'.1 0 ∨ e.1 1 = e'.1 1) → e = e')
    (hmin : ∀ c ∈ F.image (fun e => e.1 2),
      H ≤ (F.filter (fun e => e.1 2 = c)).card)
    (hclosed : ∀ ex ∈ F, ∀ ey ∈ F, ∀ ez ∈ F,
      CWQ6CoupledCoordinatewiseSupported
        (cwQ6CoupledMixedAddress ex.1 ey.1 ez.1) →
      ∃ e' ∈ E,
        e'.1 0 = ex.1 0 ∧ e'.1 1 = ey.1 1 ∧ e'.1 2 = ez.1 2) :
    Nonempty (CWQ6PrimaryHashFamily N L G
      (F.image (fun e => e.1 2)).card H) := by
  classical
  obtain ⟨F', hF'F, himage, huniform⟩ :=
    mme_finset_uniform_positive_fiber_truncation
      F (fun e => e.1 2) H hH hmin
  have hF'E : F' ⊆ E := fun _ he => hFE (hF'F he)
  have hisolated' : ∀ e ∈ F', ∀ e' ∈ E,
      (e.1 0 = e'.1 0 ∨ e.1 1 = e'.1 1) → e = e' := by
    intro e he e' he' hcollision
    exact hisolated e (hF'F he) e' he' hcollision
  have hclosed' : ∀ ex ∈ F', ∀ ey ∈ F', ∀ ez ∈ F',
      CWQ6CoupledCoordinatewiseSupported
        (cwQ6CoupledMixedAddress ex.1 ey.1 ez.1) →
      ∃ e' ∈ E,
        e'.1 0 = ex.1 0 ∧ e'.1 1 = ey.1 1 ∧ e'.1 2 = ez.1 2 := by
    intro ex hex ey hey ez hez hsupp
    exact hclosed ex (hF'F hex) ey (hF'F hey) ez (hF'F hez) hsupp
  rw [← himage]
  exact mme_CW_q6_uniform_isolated_address_set_to_hash_family
    N L G H E F' hH hF'E hisolated' huniform hclosed'
