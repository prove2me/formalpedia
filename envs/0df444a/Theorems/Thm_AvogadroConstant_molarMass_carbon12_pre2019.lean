-- Prove2me | Theorems.Thm_AvogadroConstant_molarMass_carbon12_pre2019
-- name    : AvogadroConstant.molarMass_carbon12_pre2019
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T18:28:19.335987+00:00
-- url     : https://prove2.me/theorems/cee9017d-74f5-451c-89da-1327e4d25605
-- title:
--   Pre-2019: a $12\,\mathrm{Da}$ particle has molar mass $12\,\mathrm{g}/\mathrm{mol}$
-- statement:
--   Under the pre-2019 definition of the mole, the numerical value of the mass of one mole of a
--   substance expressed in grams equalled the average mass of one particle expressed in daltons. This
--   lemma is that statement in the case of carbon-12, from which the convention was derived.
--
--   Let $U$ be a unit system and suppose the Avogadro constant is the gram-to-dalton ratio per mole,
--
--   $$ N_A = \frac{\mathrm{g}/\mathrm{Da}}{\mathrm{mol}} . $$
--
--   Then a particle of mass $12\,\mathrm{Da}$ has molar mass $M = (12\,\mathrm{Da})\,N_A$ equal to
--
--   $$ 12\,\frac{\mathrm{g}}{\mathrm{mol}} . $$
--
--   Since the 2019 revision this numerical equivalence is no longer exact, because $N_A$ is now fixed
--   while the dalton is measured; the lemma isolates the hypothesis under which it is exact.
--
--   **Formalization Note** The hypothesis on $N_A$ is given as an explicit equation rather than taken
--   from the fixed 2019 value, precisely so that the pre-2019 regime can be stated.
-- source:
--   Wikipedia, "Avogadro constant" (uploaded PDF snapshot), sections "Definition" and "History / X-ray crystallography"; SI 2019 redefinition of the mole, https://en.wikipedia.org/wiki/Avogadro_constant

import Mathlib
import Definitions.Def_AvogadroConstant_model

namespace AvogadroConstant
theorem molarMass_carbon12_pre2019
    (U : MassAmountUnits) (NA : ℝ) (hNA : NA = U.gram / U.dalton / U.mole) :
    molarMass NA (12 * U.dalton) = 12 * U.gram / U.mole := by sorry
end AvogadroConstant
