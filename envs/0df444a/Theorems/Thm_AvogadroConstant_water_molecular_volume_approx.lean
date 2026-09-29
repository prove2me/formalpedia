-- Prove2me | Theorems.Thm_AvogadroConstant_water_molecular_volume_approx
-- name    : AvogadroConstant.water_molecular_volume_approx
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T18:29:28.465836+00:00
-- url     : https://prove2.me/theorems/ad5c4e0b-dee1-43e4-a72b-623d96de9917
-- title:
--   Volume of one water molecule: between $0.0298$ and $0.0300\ \mathrm{nm}^3$
-- statement:
--   The source's worked example: since the molar volume of water in ordinary conditions is about
--   $18\ \mathrm{mL}/\mathrm{mol}$, the volume occupied by one molecule of water is about
--   $18/(6.022\times10^{23})\ \mathrm{mL}$, that is about $0.030\ \mathrm{nm}^3$.
--
--   Let $U$ be a unit system, let $\mathrm{nm}^3 > 0$ be a volume unit and let
--   $\mathrm{mL} = 10^{21}\,\mathrm{nm}^3$ (one millilitre is one cubic centimetre, hence $10^{21}$ cubic
--   nanometres). Let $v$ be the volume occupied by one molecule, so that its molar volume is
--   $V_m = v\,N_A$ with $N_A = N_0/\mathrm{mol}$, and assume that one mole of water occupies 18 mL:
--
--   $$ V_m \cdot \mathrm{mol} = 18\,\mathrm{mL}. $$
--
--   Then
--
--   $$ 0.0298\,\mathrm{nm}^3 \;<\; v \;<\; 0.0300\,\mathrm{nm}^3 . $$
--
--   **Formalization Note** $N_0$ is the exact rational $602214076\times10^{15}$, so the bounds are
--   strict rational inequalities rather than a floating-point rounding statement; the two-sided form
--   prevents the claim from being satisfied by an arbitrary rounded value.
-- source:
--   Wikipedia, "Avogadro constant" (uploaded PDF snapshot), sections "Definition" and "History / X-ray crystallography"; SI 2019 redefinition of the mole, https://en.wikipedia.org/wiki/Avogadro_constant

import Mathlib
import Definitions.Def_AvogadroConstant_model

namespace AvogadroConstant
theorem water_molecular_volume_approx
    (U : MassAmountUnits) (mL nm3 v : ℝ) (hnm3 : 0 < nm3) (hmL : mL = 10 ^ 21 * nm3)
    (hv : molarVolume (avogadroConstant U) v * U.mole = 18 * mL) :
    0.0298 * nm3 < v ∧ v < 0.0300 * nm3 := by sorry
end AvogadroConstant
