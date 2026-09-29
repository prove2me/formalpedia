-- Prove2me | Theorems.Thm_AvogadroConstant_avogadroNumber_eq_gram_div_dalton
-- name    : AvogadroConstant.avogadroNumber_eq_gram_div_dalton
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T17:47:19.902751+00:00
-- url     : https://prove2.me/theorems/fb70961d-d2b1-44b6-b356-a76f031e78ba
-- title:
--   Avogadro number as the gram-to-dalton ratio, $N_0 = \mathrm{g}/\mathrm{Da}$
-- statement:
--   **Goal theorem of the mission.** This is the pre-2019 definition of the mole, in the form stated in
--   the source: the Avogadro number was "the number of daltons in a gram", $N_0 = \mathrm{g}/\mathrm{Da}$.
--
--   Fix a unit system consisting of a gram $\mathrm{g} > 0$, a dalton $\mathrm{Da} > 0$ and a mole
--   $\mathrm{mol} > 0$. Let $m_{\mathrm{C}} > 0$ be the mass of a single carbon-12 atom, and let $N$ be
--   a real number. Assume
--
--   1. $N\,m_{\mathrm{C}} = 12\,\mathrm{g}$ — a sample of $N$ carbon-12 atoms has mass exactly 12 grams,
--      which is the old definition of one mole of carbon-12; and
--   2. $\mathrm{Da} = m_{\mathrm{C}}/12$ — the dalton is one twelfth of the mass of a carbon-12 atom.
--
--   Then
--
--   $$ N = \frac{\mathrm{g}}{\mathrm{Da}} . $$
--
--   The statement fixes no numerical value: it says that the count defining the old mole coincides with
--   the gram-to-dalton mass ratio, which is why the 2019 redefinition — fixing $N_0$ and leaving the
--   dalton to be measured — turns this exact identity into an approximate one.
--
--   **Formalization Note** Units are positive real parameters; the hypotheses are simultaneously
--   satisfiable, so the statement is not vacuous.
-- source:
--   Wikipedia, "Avogadro constant" (uploaded PDF snapshot), sections "Definition" and "History / X-ray crystallography"; SI 2019 redefinition of the mole, https://en.wikipedia.org/wiki/Avogadro_constant

import Mathlib
import Definitions.Def_AvogadroConstant_model

namespace AvogadroConstant
theorem avogadroNumber_eq_gram_div_dalton
    (U : MassAmountUnits) (mC12 : ℝ) (hmC12 : 0 < mC12) (N : ℝ)
    (hmole : N * mC12 = 12 * U.gram) (hdalton : U.dalton = mC12 / 12) :
    N = U.gram / U.dalton := by sorry
end AvogadroConstant
