-- Prove2me | Theorems.Thm_AvogadroConstant_molarMass_mul_mole_eq_avogadroNumber_mul_mass
-- name    : AvogadroConstant.molarMass_mul_mole_eq_avogadroNumber_mul_mass
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T18:14:31.611642+00:00
-- url     : https://prove2.me/theorems/4783a232-1cd3-4979-b66c-52a8a9fe4101
-- title:
--   SI 2019: the mass of one mole is $N_0$ times the entity mass
-- statement:
--   Since the 2019 revision of the SI, the mass of one mole of a substance is exactly the product of the
--   Avogadro number and the average mass of one of the entities involved.
--
--   Let $U$ be a unit system, $N_A = N_0/\mathrm{mol}$ with $N_0 = 6.02214076\times10^{23}$, and let $m$
--   be the average mass of one entity. Its molar mass is $M = m\,N_A$, a mass per amount of substance.
--   Multiplying by one mole gives the mass of one mole:
--
--   $$ M \cdot \mathrm{mol} = N_0 \cdot m . $$
--
--   The identity records that the mole-to-entity conversion is carried entirely by the pure number
--   $N_0$, with the unit $\mathrm{mol}$ cancelling.
--
--   **Formalization Note** The statement holds for every real $m$; positivity of $\mathrm{mol}$ comes
--   from the unit system.
-- source:
--   Wikipedia, "Avogadro constant" (uploaded PDF snapshot), sections "Definition" and "History / X-ray crystallography"; SI 2019 redefinition of the mole, https://en.wikipedia.org/wiki/Avogadro_constant

import Mathlib
import Definitions.Def_AvogadroConstant_model

namespace AvogadroConstant
theorem molarMass_mul_mole_eq_avogadroNumber_mul_mass (U : MassAmountUnits) (m : ℝ) :
    molarMass (avogadroConstant U) m * U.mole = avogadroNumber * m := by sorry
end AvogadroConstant
