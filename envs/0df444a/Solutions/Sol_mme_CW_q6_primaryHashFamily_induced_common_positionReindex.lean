-- Prove2me | solution 1 for mme_CW_q6_primaryHashFamily_induced_common_positionReindex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T10:53:17.620116+00:00
-- url     : https://prove2.me/submissions/31e2e8f3-3cef-4923-89b4-36630131e4e9

import Mathlib.Tactic
import Theorems.Thm_mme_CW_q6_coordinatewiseSupported_positionReindex_iff

open MME

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {N L G A H : ℕ} (family : CWQ6PrimaryHashFamily N L G A H)
    (rho : Equiv.Perm (Fin (2 * N)))
    (p q r : Fin A × Fin H)
    (hsupport : CWQ6CoupledCoordinatewiseSupported
      (cwQ6CoupledMixedAddress
        (cwQ6CoupledAddressPositionReindex rho (family.entry p).1)
        (cwQ6CoupledAddressPositionReindex rho (family.entry q).1)
        (cwQ6CoupledAddressPositionReindex rho (family.entry r).1))) :
    p = q ∧ p.1 = r.1 := by
  have hmixed :
      cwQ6CoupledMixedAddress
          (cwQ6CoupledAddressPositionReindex rho (family.entry p).1)
          (cwQ6CoupledAddressPositionReindex rho (family.entry q).1)
          (cwQ6CoupledAddressPositionReindex rho (family.entry r).1) =
        cwQ6CoupledAddressPositionReindex rho
          (cwQ6CoupledMixedAddress
            (family.entry p).1 (family.entry q).1 (family.entry r).1) := by
    funext i j
    fin_cases i <;> rfl
  rw [hmixed] at hsupport
  exact family.induced p q r
    ((mme_CW_q6_coordinatewiseSupported_positionReindex_iff rho _).mp
      hsupport)
