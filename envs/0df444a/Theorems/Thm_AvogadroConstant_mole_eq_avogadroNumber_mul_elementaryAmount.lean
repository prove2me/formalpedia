-- Prove2me | Theorems.Thm_AvogadroConstant_mole_eq_avogadroNumber_mul_elementaryAmount
-- name    : AvogadroConstant.mole_eq_avogadroNumber_mul_elementaryAmount
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T18:21:55.450083+00:00
-- url     : https://prove2.me/theorems/3c87110c-b5d7-4b8f-82a2-4836189b641a
-- title:
--   $1\ \mathrm{mol} = N_0\,n_a$ for the elementary amount $n_a = 1/N_A$
-- statement:
--   An amount of substance consisting of a single elementary entity may be called the **elementary
--   amount** $n_a$. Since one mole contains $N_0$ entities, $1\,\mathrm{mol} = N_0\,n_a$, and the
--   Avogadro constant is the reciprocal of the elementary amount, $N_A = 1/n_a$ — a characterization
--   independent of the choice of macroscopic base unit.
--
--   Formally, for a unit system $U$ with mole unit $\mathrm{mol} > 0$, put $N_A = N_0/\mathrm{mol}$ and
--   $n_a = 1/N_A$. Then
--
--   $$ \mathrm{mol} = N_0 \cdot n_a . $$
--
--   **Formalization Note** The identity is stated for the mole unit of an arbitrary unit system; both
--   $\mathrm{mol} > 0$ and $N_0 > 0$ are used to invert the divisions.
-- source:
--   Wikipedia, "Avogadro constant" (uploaded PDF snapshot), sections "Definition" and "History / X-ray crystallography"; SI 2019 redefinition of the mole, https://en.wikipedia.org/wiki/Avogadro_constant

import Mathlib
import Definitions.Def_AvogadroConstant_model

namespace AvogadroConstant
theorem mole_eq_avogadroNumber_mul_elementaryAmount (U : MassAmountUnits) :
    U.mole = avogadroNumber * elementaryAmount (avogadroConstant U) := by sorry
end AvogadroConstant
