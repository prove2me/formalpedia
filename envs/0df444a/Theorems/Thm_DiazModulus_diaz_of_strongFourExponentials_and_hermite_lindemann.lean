-- Prove2me | Theorems.Thm_DiazModulus_diaz_of_strongFourExponentials_and_hermite_lindemann
-- name    : DiazModulus.diaz_of_strongFourExponentials_and_hermite_lindemann
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-07T06:46:14.627715+00:00
-- url     : https://prove2.me/theorems/3c858325-aec9-420c-bdaf-c57c6a4942c6
-- title:
--   The strong four exponentials conjecture, with Hermite--Lindemann, implies Diaz's modulus conjecture
-- statement:
--   **The strong four exponentials conjecture implies Diaz's conjecture.**
--
--   The second implication Diaz records, and the sharper of the two: the whole argument is a single $2\times2$ configuration.
--
--   Let $u \neq 0$ have $\lambda = |u|$ algebraic and $e^{u}$ algebraic. Put
--   $$x_1 = u,\quad x_2 = \lambda,\qquad y_1 = 1,\quad y_2 = \lambda/u .$$
--   The four products are
--   $$x_1y_1 = u,\quad x_1y_2 = \lambda,\quad x_2y_1 = \lambda,\quad x_2y_2 = \frac{\lambda^{2}}{u} = \bar u,$$
--   the last equality by `DiazModulus.conj_eq_norm_sq_div`. All four lie in $\tilde{\mathcal L}$: $u \in \mathcal{L}$ by hypothesis, $\bar u \in \mathcal{L}$ by `DiazModulus.logAlg_conj_stable`, and $\lambda \in \bar{\mathbb{Q}} \subseteq \tilde{\mathcal L}$.
--
--   Both pairs are $\bar{\mathbb{Q}}$-linearly independent for the same single reason: $\{u,\lambda\}$ is dependent exactly when $u \in \bar{\mathbb{Q}}$ (as $\lambda \neq 0$ is algebraic), and $\{1, \lambda/u\}$ is dependent exactly when $\lambda/u \in \bar{\mathbb{Q}}$, again exactly when $u \in \bar{\mathbb{Q}}$. And $u \notin \bar{\mathbb{Q}}$ is Hermite--Lindemann applied to the hypothesis that $e^{u}$ is algebraic. So the strong four exponentials conjecture is contradicted.
--
--   **Here `HermiteLindemann` really is needed as a hypothesis, and the declaration's name says so.** Unlike Schanuel, the four-exponentials statement does not visibly imply it, so it is carried explicitly. The configuration itself is the one recorded by Waldschmidt with $y_1 = \lambda$, $y_2 = |\lambda|$; what this milestone supplies is the verification that its independence hypotheses hold and that all four products land in $\tilde{\mathcal L}$.
-- source:
--   G. Diaz, Utilisation de la conjugaison complexe dans l'etude de la transcendance de valeurs de la fonction exponentielle usuelle, J. Theor. Nombres Bordeaux 16 (2004), no. 3, 535-553, doi:10.5802/jtnb.459, section 5.1, p. 550; M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer 2000, p. 15 (the configuration) and p. 399

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus
theorem diaz_of_strongFourExponentials_and_hermite_lindemann
    (hS : StrongFourExponentials) (hHL : HermiteLindemann) :
    DiazModulusConjecture := by sorry
end DiazModulus
