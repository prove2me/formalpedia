-- Prove2me | Theorems.Thm_DiazModulus_candidate_pair_dichotomy
-- name    : DiazModulus.candidate_pair_dichotomy
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-04T18:32:51.793696+00:00
-- url     : https://prove2.me/theorems/05ec7995-333b-4521-bada-128a331448cc
-- title:
--   Two candidates with a rational ratio of squared moduli: one is a rational multiple of the other or of its conjugate exactly when they are algebraically dependent
-- statement:
--   Let $u, v$ be candidates for Diaz's conjecture (`DiazModulus.IsCandidate`) with $|v|^2 = m\,|u|^2$ for some $m \in \mathbb{Q}$. Then $v \in \mathbb{Q}^\times u \cup \mathbb{Q}^\times\bar u$ if and only if $u$ and $v$ are algebraically dependent over $\mathbb{Q}$. So exactly one of two things holds: $v \in \mathbb{Q}^\times u \cup \mathbb{Q}^\times\bar u$, or $u$ and $v$ are algebraically independent.
--
--   This is Theorem 2.5 of C. Perassi's unpublished manuscript on Diaz's modulus conjecture, where it was derived from Roy and Waldschmidt (1997); here it follows from the four exponentials theorem in transcendence degree one. It concerns candidates, so it is vacuous if Diaz's conjecture holds.
--
--   **Proof.** If $v \in \mathbb{Q}^\times u \cup \mathbb{Q}^\times\bar u$, then $u$ and $v$ are dependent (`Diaz.pair_dichotomy_exclusive`). Conversely, if they are dependent, they generate an algebra of transcendence degree at most one ($u$ is transcendental by Hermite–Lindemann), and so do $u, v, \bar u, \bar v$, since $\bar u = |u|^2/u$ and $\bar v = |v|^2/v$ with algebraic numerators. Then `DiazModulus.log_pair_rigid_of_trdeg_one` gives $v \in \mathbb{Q}u \cup \mathbb{Q}\bar u$, with a non-zero factor since $v \neq 0$.
--
--   **Novelty.** Not asserted. It is Waldschmidt's Corollary 4 (1973, p. 192) at $(mu, \bar u, v)$.
-- source:
--   Theorem 2.5 of C. Perassi, unpublished manuscript on Diaz's modulus conjecture (August 2026). A direct instance of M. Waldschmidt, Solution du huitième problème de Schneider, J. Number Theory 5 (1973), 191–202, Cor. 4 (p. 192), at (mu, ū, v); the manuscript's route through D. Roy and M. Waldschmidt, Approximation diophantienne et indépendance algébrique de logarithmes, Ann. Sci. École Norm. Sup. (4) 30 (1997), 753–796, Th. 0.2, is not needed. Exclusivity is Diaz.pair_dichotomy_exclusive. Formal proof: Diaz modulus mission, 4 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem candidate_pair_dichotomy (u v : ℂ) (hu : IsCandidate u) (hv : IsCandidate v)
    (m : ℚ) (hm : v * conj v = (m : ℂ) * (u * conj u)) :
    ((∃ c : ℚ, c ≠ 0 ∧ v = (c : ℂ) * u) ∨ (∃ c : ℚ, c ≠ 0 ∧ v = (c : ℂ) * conj u)) ↔
      ¬ AlgebraicIndependent ℚ ![u, v] := by
  sorry

end DiazModulus
