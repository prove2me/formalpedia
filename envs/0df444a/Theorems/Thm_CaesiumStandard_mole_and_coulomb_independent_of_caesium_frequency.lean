-- Prove2me | Theorems.Thm_CaesiumStandard_mole_and_coulomb_independent_of_caesium_frequency
-- name    : CaesiumStandard.mole_and_coulomb_independent_of_caesium_frequency
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T18:44:07.699973+00:00
-- url     : https://prove2.me/theorems/3dd0ae4f-e891-4ac4-b2df-ae51b5f9d079
-- title:
--   Only the mole and the coulomb are independent of $\Delta\nu_{\mathrm{Cs}}$
-- statement:
--   **Which unit formulas depend on the caesium frequency.**
--
--   Take the *Summary* formulas for the seven base units and the *Electromagnetic units* formula for
--   the coulomb, and let the caesium frequency vary while the other defining constants stay at their
--   fixed values. Write $s(\nu), m(\nu), \mathrm{kg}(\nu), \mathrm A(\nu), \mathrm K(\nu),
--   \mathrm{mol}(\nu), \mathrm{cd}(\nu), \mathrm C(\nu)$ for the resulting values at frequency $\nu$.
--   Then
--
--   $$\mathrm{mol}(\nu_1) = \mathrm{mol}(\nu_2)\quad\text{and}\quad \mathrm C(\nu_1) = \mathrm C(\nu_2)
--   \qquad\text{for all }\nu_1,\nu_2,$$
--
--   while for all $\nu_1,\nu_2 > 0$ with $\nu_1 \ne \nu_2$,
--
--   $$s(\nu_1)\ne s(\nu_2),\quad m(\nu_1)\ne m(\nu_2),\quad \mathrm{kg}(\nu_1)\ne \mathrm{kg}(\nu_2),
--   \quad \mathrm A(\nu_1)\ne \mathrm A(\nu_2),\quad \mathrm K(\nu_1)\ne \mathrm K(\nu_2),
--   \quad \mathrm{cd}(\nu_1)\ne \mathrm{cd}(\nu_2).$$
--
--   This is the source's closing observation: six of the seven base units have values that depend on
--   $\Delta\nu_{\mathrm{Cs}}$, the mole does not, and the coulomb — an ampere second — is independent
--   of $\Delta\nu_{\mathrm{Cs}}$ even though the ampere is not.
-- source:
--   "Caesium standard", Wikipedia, revision 1328818072, https://en.wikipedia.org/w/index.php?title=Caesium_standard&oldid=1328818072 — section 'Summary'

import Definitions.Def_CaesiumStandard_constants

namespace CaesiumStandard

theorem mole_and_coulomb_independent_of_caesium_frequency :
    (∀ nu₁ nu₂ : ℚ, moleIn nu₁ = moleIn nu₂)
    ∧ (∀ nu₁ nu₂ : ℚ, coulombIn nu₁ = coulombIn nu₂)
    ∧ (∀ nu₁ nu₂ : ℚ, 0 < nu₁ → 0 < nu₂ → nu₁ ≠ nu₂ →
        secondIn nu₁ ≠ secondIn nu₂
        ∧ metreIn nu₁ ≠ metreIn nu₂
        ∧ kilogramIn nu₁ ≠ kilogramIn nu₂
        ∧ ampereIn nu₁ ≠ ampereIn nu₂
        ∧ kelvinIn nu₁ ≠ kelvinIn nu₂
        ∧ candelaIn nu₁ ≠ candelaIn nu₂) := by sorry

end CaesiumStandard
