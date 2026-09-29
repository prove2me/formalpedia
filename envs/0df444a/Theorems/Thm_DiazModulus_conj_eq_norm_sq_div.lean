-- Prove2me | Theorems.Thm_DiazModulus_conj_eq_norm_sq_div
-- name    : DiazModulus.conj_eq_norm_sq_div
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-07T06:44:06.530554+00:00
-- url     : https://prove2.me/theorems/d3b1bf2c-d668-43b5-905f-36b71b8b63c9
-- title:
--   $\bar u = |u|^{2}/u$
-- statement:
--   For every complex number $u$,
--   $$\bar u \;=\; \frac{|u|^{2}}{u},$$
--   immediately from $u\bar u = |u|^{2}$.
--
--   **No hypothesis $u \neq 0$ is imposed, and none is needed.** At $u = 0$ both sides are $0$, since division by zero returns $0$ in this setting; the $u = 0$ instance therefore holds by that convention rather than by ordinary mathematics, and the statement is the unrestricted identity. The squared quantity is the real norm $\lVert u\rVert$ cast into $\mathbb{C}$ and then squared, which agrees in value with $u\bar u$.
--
--   It is stated on its own because it is the hinge of the whole configuration. If $u$ is a candidate counterexample to the mission goal then $|u|^{2}$ is algebraic, so this identity says that $\bar u$ is a **rational function of $u$ with algebraic coefficients**. Two consequences run through the mission in opposite directions.
--
--   Constructively, it is what lets the four-exponentials configuration be written down at all: the four products in `DiazModulus.diaz_of_strongFourExponentials_and_hermite_lindemann` are $u$, $\lambda$, $\lambda$ and $\lambda^{2}/u = \bar u$, and the last equality is this lemma.
--
--   Destructively, it is why a large class of attacks cannot work. Complex conjugation on $\bar{\mathbb{Q}}(u)$ is determined by the ring structure rather than being independent data, so no accumulation of algebraic relations between $u$ and $\bar u$ can separate a candidate from an ordinary complex number placed on the same circle. See the mission description.
-- source:
--   G. Diaz, Utilisation de la conjugaison complexe dans l'etude de la transcendance de valeurs de la fonction exponentielle usuelle, J. Theor. Nombres Bordeaux 16 (2004), no. 3, 535-553, doi:10.5802/jtnb.459, section 5.1, p. 550

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus
theorem conj_eq_norm_sq_div (u : ℂ) :
    conj u = ((‖u‖ : ℝ) : ℂ) ^ 2 / u := by sorry
end DiazModulus
