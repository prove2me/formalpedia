-- Prove2me | Theorems.Thm_AvogadroConstant_crystal_amountOfSubstance
-- name    : AvogadroConstant.crystal_amountOfSubstance
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T18:29:51.759257+00:00
-- url     : https://prove2.me/theorems/b7e4bbaa-1347-4853-9379-1b5d395224b6
-- title:
--   Crystal versus unit cell: amount of substance of a crystal
-- statement:
--   For a crystalline substance, the Avogadro constant relates the volume of a crystal to that of its
--   unit cell — the relation underlying X-ray crystal density measurements, in which the unit-cell
--   dimensions of a very pure crystal are measured by X-ray diffraction.
--
--   Let $U$ be a unit system with mole unit $\mathrm{mol} > 0$, let a crystal have volume $V$, and let
--   its unit cell have volume $v_{\text{cell}} > 0$ and contain $k$ elementary entities, where $k$ is a
--   natural number. The crystal then contains $k\,V/v_{\text{cell}}$ entities, and its amount of
--   substance $n = (k\,V/v_{\text{cell}})/N_A$, with $N_A = N_0/\mathrm{mol}$, equals
--
--   $$ n \;=\; \frac{k\,V}{v_{\text{cell}}\,N_0}\,\mathrm{mol}. $$
--
--   Read in the other direction, a measurement of $V$, $v_{\text{cell}}$ and $n$ determines $N_0$.
--
--   **Formalization Note** $V$ is an arbitrary real (no positivity is required for the identity);
--   $v_{\text{cell}} > 0$ is assumed, and $k$ is a natural number cast to a real.
-- source:
--   Wikipedia, "Avogadro constant" (uploaded PDF snapshot), sections "Definition" and "History / X-ray crystallography"; SI 2019 redefinition of the mole, https://en.wikipedia.org/wiki/Avogadro_constant

import Mathlib
import Definitions.Def_AvogadroConstant_model

namespace AvogadroConstant
theorem crystal_amountOfSubstance
    (U : MassAmountUnits) (V vCell : ℝ) (k : ℕ) (hvCell : 0 < vCell) :
    amountOfSubstance (avogadroConstant U) (crystalEntityCount V vCell k)
      = (k : ℝ) * V / (vCell * avogadroNumber) * U.mole := by sorry
end AvogadroConstant
