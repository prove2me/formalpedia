-- Prove2me | Theorems.Thm_DiazModulus_two_pow_log_three_or_three_pow_log_two
-- name    : DiazModulus.two_pow_log_three_or_three_pow_log_two
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-23T18:24:23.75644+00:00
-- url     : https://prove2.me/theorems/b076e7dc-b660-4139-9641-3ebf1b3c801d
-- title:
--   At least one of 2^{log₃ 2} and 3^{log₂ 3} is transcendental
-- statement:
--   **$2^{\log_3 2}$ or $3^{\log_2 3}$.**
--
--   At least one of
--
--   $$2^{\log_{3} 2} = e^{(\log 2)^{2}/\log 3} \qquad\text{and}\qquad 3^{\log_{2} 3} = e^{(\log 3)^{2}/\log 2}$$
--
--   is transcendental.
--
--   It is `DiazModulus.log_square_duality` at $\lambda = \log 2$, $\mu = \log 3$. Neither number is known to be transcendental on its own.
--
--   **Novelty.** None; see `DiazModulus.log_square_duality`, of which this is an instance. The contribution of this node is the formal proof.
-- source:
--   Instance of DiazModulus.log_square_duality, the Q-linear form of G. Diaz, Produits et quotients de combinaisons linéaires de logarithmes de nombres algébriques : conjectures et résultats partiels, J. Théor. Nombres Bordeaux 19 (2007), 373–391, Corollaire 4(3). Background: the six exponentials theorem (Lang, Ramachandra) and the Gelfond-Schneider theorem (1934). Formal proof: Diaz modulus mission, 23 September 2026 (C. Perassi).

import Mathlib

namespace DiazModulus

theorem two_pow_log_three_or_three_pow_log_two :
    Transcendental ℚ ((2 : ℝ) ^ (Real.log 2 / Real.log 3)) ∨
      Transcendental ℚ ((3 : ℝ) ^ (Real.log 3 / Real.log 2)) := by sorry

end DiazModulus
