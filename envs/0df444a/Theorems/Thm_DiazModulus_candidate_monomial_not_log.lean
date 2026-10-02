-- Prove2me | Theorems.Thm_DiazModulus_candidate_monomial_not_log
-- name    : DiazModulus.candidate_monomial_not_log
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-23T15:59:40.092562+00:00
-- url     : https://prove2.me/theorems/c5aa13f4-d6e3-4f2f-9907-72b98603d5bf
-- title:
--   No renormalised power of a candidate is a logarithm of an algebraic number
-- statement:
--   **Renormalised powers of a candidate.**
--
--   Let $u$ be a candidate for Diaz's conjecture: $u \neq 0$, with $|u|$ and $\mathrm{e}^{u}$ both algebraic. Write $\rho = |u|^{2}$. Let $k \ge 2$ be an integer and $c$ a non-zero algebraic number with $|c|^{2}\rho^{k-1} \in \mathbb{Q}$. Then
--
--   $$\mathrm{e}^{c\,u^{k}} \ \text{is transcendental.}$$
--
--   In particular $\mathrm{e}^{u^{k}/|u|^{k-1}}$ is transcendental for every $k \ge 2$, for instance $\mathrm{e}^{u^{2}/|u|}$. If $|u|^{2}$ is rational, then $\mathrm{e}^{u^{k}}$ is transcendental for every $k \ge 2$. Negative exponents reduce to this case, because $c\,u^{-k} = (c/\rho^{k})\,\bar u^{k}$ and $\bar u$ is a candidate with the same modulus.
--
--   The stronger exclusion $u^{2} \notin \widetilde{\mathcal{L}}$ recorded in `DiazModulus.candidate_multiplier_module` rests on Roy's strong six exponentials theorem, which is not formalised. The present statement is the part of that exclusion reachable from the proved four exponentials theorem in transcendence degree one alone. Like every exclusion in this mission it concerns a hypothetical counterexample, and it is vacuous if Diaz's conjecture holds.
--
--   **Formalization note.** The rationality hypothesis is written $c\,\bar c\,(u\bar u)^{k-1} = q$ with $q \in \mathbb{Q}$.
--
--   **Novelty.** The statement is a direct consequence of the four exponentials theorem in transcendence degree one (Brownawell 1974; Waldschmidt 1973). Its case $k = 3$ also follows from Corollaire 5(2) of G. Diaz (J. Théor. Nombres Bordeaux 19, 2007, p. 383), a consequence of Roy's strong six exponentials theorem, since $u^{3}/\rho = u^{2}/\bar u$; Corollaire 5(1) there gives the case $k = 2$, $u^{2}/\rho = u/\bar u$, when $1$, $u$, $\bar u$ are linearly independent over $\overline{\mathbb{Q}}$.
--   Novelty is not asserted.
-- source:
--   Carlo Perassi, companion note to https://github.com/carlok/diaz-modulus-lean, version 1.9, 25 September 2026 (GitHub release note-v1.9), Corollary 6.8. Novelty is not asserted. Formal proof: Diaz modulus mission, 23 September 2026 (C. Perassi). Background: W. D. Brownawell, The algebraic independence of certain numbers related by the exponential function, J. Number Theory 6 (1974); M. Waldschmidt, Solution du huitième problème de Schneider, J. Number Theory 5 (1973); D. Roy and M. Waldschmidt, Quadratic relations between logarithms of algebraic numbers, Proc. Japan Acad. Ser. A 71 (1995).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem candidate_monomial_not_log (u c : ℂ) (hu : IsCandidate u)
    (hc : IsAlgebraic ℚ c) (hc0 : c ≠ 0) (k : ℕ) (hk : 2 ≤ k)
    (hrat : ∃ q : ℚ, c * conj c * (u * conj u) ^ (k - 1) = (q : ℂ)) :
    Transcendental ℚ (Complex.exp (c * u ^ k)) := by sorry

end DiazModulus
