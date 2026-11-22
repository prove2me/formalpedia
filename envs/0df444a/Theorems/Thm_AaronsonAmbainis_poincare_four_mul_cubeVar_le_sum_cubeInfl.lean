-- Prove2me | Theorems.Thm_AaronsonAmbainis_poincare_four_mul_cubeVar_le_sum_cubeInfl
-- name    : AaronsonAmbainis.poincare_four_mul_cubeVar_le_sum_cubeInfl
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-07T21:27:35.678202+00:00
-- url     : https://prove2.me/theorems/93825403-8a94-4b58-bdb7-a98f6cef434f
-- title:
--   Poincar\'e inequality on the Boolean cube: $4\operatorname{Var}[p]\le\sum_i\operatorname{Inf}_i[p]$
-- statement:
--   The Poincare inequality on the Boolean cube, in the influence normalisation used by Aaronson and Ambainis.
--
--   Let $p$ be a real polynomial in $N$ variables, regarded as a function on $\{0,1\}^N$ under the uniform distribution, and let $\operatorname{Var}[p]$ and $\operatorname{Inf}_i[p]=\mathbb{E}\big[(p(x)-p(x^{\oplus i}))^2\big]$ be as in the imported definitions. Then
--
--   $$4\operatorname{Var}[p]\;\le\;\sum_{i=1}^{N}\operatorname{Inf}_i[p].$$
--
--   The inequality holds for every function on the cube; no bound on the degree of $p$ is needed. It is the elementary lower bound against which the Aaronson--Ambainis conjecture is measured: it yields a coordinate of influence at least $4\operatorname{Var}[p]/N$, which degrades with the number of variables, whereas the conjecture asks for a bound depending only on the variance and the degree.
--
--   The constant $4$ is sharp. Equality holds for the dictator $p(x)=x_1$, where $\operatorname{Var}[p]=1/4$ and the influence sum equals $1$.
--
--   **Formalization Note** The factor $4$ reflects a difference of convention rather than of content. O'Donnell defines the discrete derivative as $D_ip(x)=\tfrac12\big(p(x^{i\mapsto1})-p(x^{i\mapsto-1})\big)$ and the influence as $\mathbb{E}[(D_ip)^2]$, so his influence is one quarter of the quantity used here; his statement $\operatorname{Var}[p]\le I[p]$ is therefore the inequality above. The source works over $\{-1,1\}^N$, but both variance and influence as defined here depend only on the values of $p$ at cube points and on the bit-flip involution, so they are unchanged by the affine relabelling between $\{0,1\}^N$ and $\{-1,1\}^N$.
-- source:
--   O'Donnell, Analysis of Boolean Functions, Cambridge Univ. Press 2014; corrected version arXiv:2105.10386, Chapter 2 (Basic concepts and social choice), the "Poincare Inequality" (named, unnumbered display, p. 52 of the arXiv PDF), stated as Var[f] <= I[f]; with Inf_i and I[f] as in Definitions 2.17 and 2.27 and D_i as in Definition 2.16. The factor 4 here converts O'Donnell's normalisation to the influence Inf_i[p] = E[(p(x) - p(x^{+i}))^2] used by Aaronson & Ambainis, arXiv:0911.0996.

import Definitions.Def_AaronsonAmbainis

namespace AaronsonAmbainis

theorem poincare_four_mul_cubeVar_le_sum_cubeInfl (N : ℕ) (p : MvPolynomial (Fin N) ℝ) :
    4 * cubeVar p ≤ ∑ i : Fin N, cubeInfl p i := by sorry

end AaronsonAmbainis
