-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_scaled_hamiltonian_variation_pairing_conserved
-- name    : BirkhoffGlobalSection.scaled_hamiltonian_variation_pairing_conserved
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-03T21:48:46.571985+00:00
-- url     : https://prove2.me/theorems/f1d5c62c-4b37-46c9-b69e-59f497d19a19
-- title:
--   Scaled hamiltonian variation pairing conserved
-- statement:
--   For supplied variational solutions of a scaled smooth Hamiltonian field that remain energy tangent, their symplectic pairing is conserved under the stated regularity hypotheses.
--
--   All displayed regularity, tangency, normalization and supplied-data hypotheses of the exact formal statement are retained.
-- source:
--   Independent extraction of component 6 of the Proved theorem BirkhoffGlobalSection.variational_symplecticity_bundle. Original verified source: Solutions/Sol_BirkhoffGlobalSection_variational_symplecticity_bundle.lean. Exact original component retained.

import Theorems.Thm_BirkhoffGlobalSection_variational_symplecticity_bundle
open BirkhoffGlobalSection Set Filter Topology
open scoped ContDiff Topology
set_option linter.unusedVariables false


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem BirkhoffGlobalSection.scaled_hamiltonian_variation_pairing_conserved :
∀ (F b : Phase → ℝ) (q v w : ℝ → Phase)
    (hF : ∀ t, ContDiffAt ℝ ∞ F (q t))
    (hb : ∀ t, DifferentiableAt ℝ b (q t))
    (hv : ∀ t, HasDerivAt v
      (fderiv ℝ (fun x => b x • hamiltonianVectorField F x) (q t) (v t)) t)
    (hw : ∀ t, HasDerivAt w
      (fderiv ℝ (fun x => b x • hamiltonianVectorField F x) (q t) (w t)) t)
    (hvE : ∀ t, fderiv ℝ F (q t) (v t) = 0)
    (hwE : ∀ t, fderiv ℝ F (q t) (w t) = 0),
    ∀ t, phaseSymplecticForm (v t) (w t) = phaseSymplecticForm (v 0) (w 0) := by sorry
