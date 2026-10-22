-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_hamiltonian_radial_characteristic_normalization
-- name    : BirkhoffGlobalSection.hamiltonian_radial_characteristic_normalization
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-30T17:26:57.689739+00:00
-- url     : https://prove2.me/theorems/e1373685-bd9d-4b4b-b1a8-c30d28199371
-- title:
--   Positive radial Hamiltonian fields normalize to the characteristic Reeb identities
-- statement:
--   In coordinates (q1,q2,p1,p2), let omega be the standard symplectic form, let alpha_y(v)=-omega(y,v)/2, and let X=(F_p,-F_q) be the coordinate Hamiltonian field at y. If alpha_y(X)>0, set R=X/alpha_y(X). Then
--
--   $$\alpha_y(R)=1,\qquad DF_y(R)=0,\qquad \omega(R,v)=0\quad\text{whenever }DF_y(v)=0,$$
--
--   and
--
--   $$\alpha_y(X)=\tfrac12 DF_y(y).$$
--
--   These are the pointwise normalization and characteristic-line identities used to identify the positive Hamiltonian direction with the Reeb direction on a regular star-shaped level. The derivative kernel is used explicitly; no manifold contact-form theorem, complete flow, clock or global page is asserted.
--
--   **Formalization Note** The statement uses the total Frechet derivative and requires only the stated positive pairing. No additional differentiability hypothesis is needed for these algebraic identities.
-- source:
--   Auxiliary coordinate form of the Reeb defining equations in Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, arXiv:1105.2077v5, p. 1, equation (2), and p. 2, characteristic-line description, https://arxiv.org/pdf/1105.2077. The coordinate primitive is translated to the workspace convention X_H=(H_p,-H_q); this is the pointwise algebraic part, not a verbatim manifold theorem.

import Definitions.Def_BirkhoffGlobalSection_TransverseHopf
open BirkhoffGlobalSection

theorem BirkhoffGlobalSection.hamiltonian_radial_characteristic_normalization (F : Phase → ℝ) (y : Phase)
    (hpos : 0 < phaseRadialContact y (hamiltonianVectorField F y)) :
    let X := hamiltonianVectorField F y
    let R := (phaseRadialContact y X)⁻¹ • X
    phaseRadialContact y R = 1 ∧
      fderiv ℝ F y R = 0 ∧
      (∀ v : Phase, fderiv ℝ F y v = 0 → phaseSymplecticForm R v = 0) ∧
      phaseRadialContact y X = fderiv ℝ F y y / 2 := by sorry
