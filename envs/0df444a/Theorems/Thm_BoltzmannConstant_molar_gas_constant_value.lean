-- Prove2me | Theorems.Thm_BoltzmannConstant_molar_gas_constant_value
-- name    : BoltzmannConstant.molar_gas_constant_value
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T15:42:29.827905+00:00
-- url     : https://prove2.me/theorems/61273ead-8e22-4a2f-83c6-eed5c504ace5
-- title:
--   $R = k_B N_A = 8.31446261815324$ J·K⁻¹·mol⁻¹ exactly
-- statement:
--   Because both $k_B$ and $N_A$ are exact defining constants of the SI since the 2019 revision, their product — the molar gas constant $R = k_B N_A$ — is exact as well, with the finite decimal value $$R = 8.31446261815324\ \mathrm{J\,K^{-1}\,mol^{-1}}.$$ Unlike the electronvolt conversion, this is an exact equality of decimals, not an approximation.
-- source:
--   Wikipedia, "Boltzmann constant" (uploaded PDF), https://en.wikipedia.org/wiki/Boltzmann_constant, section "Roles of the Boltzmann constant" (molar gas constant $8.314\,462\,618\,153\,24$ J·K⁻¹·mol⁻¹) and section "Value in different units"

import Mathlib
import Definitions.Def_boltzmann_si_basics

namespace BoltzmannConstant

theorem molar_gas_constant_value : R = 8.31446261815324 := by sorry

end BoltzmannConstant
