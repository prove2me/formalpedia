-- Prove2me | solution 1 for section5_gaussian_pi_density
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:54:03.482516+00:00
-- url     : https://prove2.me/submissions/324f588d-71d6-4d4f-b41a-1159f73bb4cf

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5GaussianTail
import Definitions.Def_Section5Verified_Section5HermiteFoundations
import Mathlib
namespace «Aux_w_53_hermite»
end «Aux_w_53_hermite»
section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Aux_w_53_hermite QuantumLTF.Example

/-! Gaussian density and tail estimates for Appendix D, Eq. 230. -/









theorem section5_gaussian_density_nonneg (n : ℕ) (x : Fin n → ℝ) :
    0 ≤ section5_gaussian_density n x := Finset.prod_nonneg (fun _ _ => (phi_pos _).le)

































end
namespace «Aux_w_53_hermite»
end «Aux_w_53_hermite»
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Aux_w_53_hermite QuantumLTF.Example
theorem solution (n : ℕ) :
    Measure.pi (fun _ : Fin n => gaussianReal 0 1) =
      (Measure.pi (fun _ : Fin n => (volume : Measure ℝ))).withDensity
        (fun x => ENNReal.ofReal (section5_gaussian_density n x)) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← ofReal_integral_eq_lintegral_ofReal (section5_gaussian_density_integrable n).integrableOn
      (Filter.Eventually.of_forall (section5_gaussian_density_nonneg n))]
  rw [Measure.restrict_pi_pi]
  change ENNReal.ofReal (∫ x, ∏ i, Aux_w_53_hermite.phi (x i)
      ∂(Measure.pi (fun i : Fin n => volume.restrict (s i)))) = _
  rw [integral_fintype_prod_eq_prod,
    ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (fun x => (Aux_w_53_hermite.phi_pos x).le))]
  apply Finset.prod_congr rfl
  intro i hi
  exact (gaussianReal_apply_eq_integral 0 one_ne_zero (s i)).symm
