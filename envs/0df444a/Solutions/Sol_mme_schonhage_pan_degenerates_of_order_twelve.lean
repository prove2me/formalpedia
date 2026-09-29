-- Prove2me | solution 1 for mme_schonhage_pan_degenerates_of_order_twelve
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T03:55:38.380617+00:00
-- url     : https://prove2.me/submissions/4c7458da-f9b9-4358-a3dc-2a77be5fe512

import Mathlib.Data.Fin.VecNotation
import Definitions.Def_mme_schonhage_pan_certificate
import Theorems.Thm_mme_schonhage_pan_Phi_coeff_low_zero
import Theorems.Thm_mme_schonhage_pan_Phi_coeff_twelve_eq

open MME

universe u

/-!
This proof exposes the explicit Schönhage--Pan polynomial family `Phi` as the
order-twelve degeneration witness.  The two imported child theorems isolate
the only expensive computations: cancellation in degrees below twelve and
identification of the degree-twelve coefficient with the target tensor.
-/

theorem solution {K : Type u} [Field K] :
    DegeneratesOfOrder
      (TensorObj.bigAdd ![
        MMObj K 1 5 22,
        MMObj K 11 2 5,
        MMObj K 10 11 1])
      (TensorObj.diagObj K 3 156) 12 := by
  refine ⟨PanLeanBridge.Phi (K := K), ?_, ?_⟩
  · exact fun n hn => mme_schonhage_pan_Phi_coeff_low_zero n hn
  · exact mme_schonhage_pan_Phi_coeff_twelve_eq
