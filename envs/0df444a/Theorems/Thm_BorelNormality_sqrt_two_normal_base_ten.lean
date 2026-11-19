-- Prove2me | Theorems.Thm_BorelNormality_sqrt_two_normal_base_ten
-- name    : BorelNormality.sqrt_two_normal_base_ten
-- status  : Open
-- author  : @LG
-- created : 2026-11-18T17:10:45.844377+00:00
-- url     : https://prove2.me/theorems/1db5490e-8101-447a-a747-ff70aff767dd
-- title:
--   Borel 1950: the decimal expansion of $\sqrt{2}$ is normal
-- statement:
--   The headline open special case of Borel's conjecture: the real number $\sqrt{2}$ is normal in base ten. Every finite block of $k$ decimal digits occurs in the decimal expansion of $\sqrt{2}$ with limiting frequency $10^{-k}$:
--
--   $$\mathrm{IsNormalReal}(10, \sqrt{2}).$$
--
--   Borel's 1950 note was specifically about the decimal digits of $\sqrt{2}$. The statement is open: it is not even known whether the digit $7$ occurs infinitely often in the decimal expansion of $\sqrt{2}$ (Adamczewski–Bugeaud 2007, Introduction). It follows from the mission's goal, since $\sqrt{2}$ is irrational and algebraic, and is the simplest concrete target on the way there.
--
--   **Formalization Note.** `Real.sqrt 2` is the nonnegative real square root of $2$; the predicate is `Normal.IsNormalReal` from `Normal_Core` at the fixed base $10$.
-- source:
--   É. Borel, Sur les chiffres décimaux de √2 et divers problèmes de probabilités en chaîne, C. R. Acad. Sci. Paris 230 (1950), 591–593; https://en.wikipedia.org/wiki/Normal_number, section 'Borel's normality conjecture'; B. Adamczewski, Y. Bugeaud, Ann. of Math. (2) 165 (2007), 547–565, Introduction (p. 547): 'we even do not know whether the digit 7 occurs infinitely often in the decimal expansion of √2.'

import Mathlib
import Definitions.Def_Normal_Core

set_option autoImplicit false

namespace BorelNormality

theorem sqrt_two_normal_base_ten : Normal.IsNormalReal 10 (Real.sqrt 2) := by sorry

end BorelNormality
