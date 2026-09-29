-- Prove2me | Theorems.Thm_AvogadroConstant_amount_mul_avogadroConstant_eq_count
-- name    : AvogadroConstant.amount_mul_avogadroConstant_eq_count
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T18:04:51.48024+00:00
-- url     : https://prove2.me/theorems/1630d377-828c-4ec2-a299-dddef2708019
-- title:
--   Amount of substance inverts the entity count: $n(X)\,N_A = N(X)$
-- statement:
--   Let $U$ be a unit system and let $N_A = N_0/\mathrm{mol}$ be the Avogadro constant, where
--   $N_0 = 6.02214076\times10^{23}$. For a sample containing $N$ elementary entities, its amount of
--   substance is $n = N/N_A$. The lemma states that this conversion is invertible in the expected way:
--
--   $$ n \cdot N_A = N . $$
--
--   Equivalently, $N(X) = n(X)\,N_A$: the number of entities is recovered from the amount of substance
--   by multiplying by the Avogadro constant. This is the defining property of $N_A$ as the
--   proportionality factor between amount of substance and number of particles.
--
--   **Formalization Note** No nondegeneracy hypothesis is needed: $N_A > 0$ follows from
--   $\mathrm{mol} > 0$, which is part of the unit-system data.
-- source:
--   Wikipedia, "Avogadro constant" (uploaded PDF snapshot), sections "Definition" and "History / X-ray crystallography"; SI 2019 redefinition of the mole, https://en.wikipedia.org/wiki/Avogadro_constant

import Mathlib
import Definitions.Def_AvogadroConstant_model

namespace AvogadroConstant
theorem amount_mul_avogadroConstant_eq_count (U : MassAmountUnits) (N : ℝ) :
    amountOfSubstance (avogadroConstant U) N * avogadroConstant U = N := by sorry
end AvogadroConstant
