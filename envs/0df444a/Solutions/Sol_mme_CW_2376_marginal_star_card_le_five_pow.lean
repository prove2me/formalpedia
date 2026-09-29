-- Prove2me | solution 1 for mme_CW_2376_marginal_star_card_le_five_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T22:40:33.347085+00:00
-- url     : https://prove2.me/submissions/902eedde-1b6b-49b9-ab99-48567074d508

import Definitions.Def_mme_CW_2376_hash_incidence_universes
import Theorems.Thm_mme_CW_2376_supported_two_modes_determine_address

open MME

set_option autoImplicit false

theorem solution
    (m : ℕ) (i : Fin 3) (a : CW2376MarginalSupportedAddress m) :
    ((cw2376MarginalSupportedUniverse m).filter
      (fun b => b.1 i = a.1 i)).card ≤
        5 ^ cw2376ProfileLength m := by
  classical
  let U := cw2376MarginalSupportedUniverse m
  let star := U.filter (fun b => b.1 i = a.1 i)
  have injectAt (k : Fin 3) (hik : i ≠ k) :
      Function.Injective
        (fun b : {b // b ∈ star} => b.1.1 k) := by
    intro b c hbc
    apply Subtype.ext
    apply Subtype.ext
    apply mme_CW_2376_supported_two_modes_determine_address
      b.1.2.1 c.1.2.1 hik
    · have hb := (Finset.mem_filter.mp b.2).2
      have hc := (Finset.mem_filter.mp c.2).2
      exact hb.trans hc.symm
    · exact hbc
  have hcard (k : Fin 3) (hik : i ≠ k) :
      star.card ≤ Fintype.card
        (Fin (cw2376ProfileLength m) → Fin 5) := by
    rw [← Fintype.card_coe]
    exact Fintype.card_le_of_injective _ (injectAt k hik)
  change star.card ≤ _
  fin_cases i
  · simpa using hcard (1 : Fin 3) (by decide)
  · simpa using hcard (2 : Fin 3) (by decide)
  · simpa using hcard (0 : Fin 3) (by decide)
