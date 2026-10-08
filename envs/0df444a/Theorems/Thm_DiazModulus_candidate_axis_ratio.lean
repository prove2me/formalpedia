-- Prove2me | Theorems.Thm_DiazModulus_candidate_axis_ratio
-- name    : DiazModulus.candidate_axis_ratio
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-04T18:32:29.697684+00:00
-- url     : https://prove2.me/theorems/4ceacade-6c53-4820-83b2-764b4e7061c3
-- title:
--   Two distinct candidates whose difference is real or purely imaginary: a rational ratio of squared moduli, equal moduli, and v = ±ū are equivalent
-- statement:
--   Let $u \neq v$ be candidates for Diaz's conjecture with $v - u$ real or purely imaginary. The following are equivalent: (i) $|v|^2/|u|^2 \in \mathbb{Q}$; (ii) $|v| = |u|$; (iii) $v = \bar u$ if $v - u$ is purely imaginary, and $v = -\bar u$ if $v - u$ is real.
--
--   This is the equivalence in Theorem 2.3 of C. Perassi's unpublished manuscript on Diaz's modulus conjecture; its last assertion is `Diaz.axis_triple_indep`. It concerns candidates, so it is vacuous if Diaz's conjecture holds.
--
--   **Proof.** (ii) and (iii) are equivalent by plane geometry: equal real parts and equal moduli force opposite imaginary parts, and equal imaginary parts and equal moduli force opposite real parts. (ii) gives (i) with ratio $1$. For (i) ⇒ (ii), the condition on $v - u$ gives $v - \bar v = u - \bar u$ or $v + \bar v = u + \bar u$. With $\bar u = |u|^2/u$ and $\bar v = |v|^2/v$, it says that $v$ satisfies a quadratic equation over $\overline{\mathbb{Q}}(u)$, so $u$ and $v$ are algebraically dependent. By `DiazModulus.candidate_pair_dichotomy`, $v = cu$ or $v = c\bar u$ with $c \in \mathbb{Q}^\times$. Candidates lie on neither axis (Hermite–Lindemann), so $v = cu$ forces $c = 1$, which is excluded, and $v = c\bar u$ forces $c = \pm 1$, hence $|v| = |u|$.
--
--   **Novelty.** Not asserted. The step (i) ⇒ (ii) is Waldschmidt's Corollary 4 (1973, p. 192) at $(mu, \bar u, v)$; the rest is elementary.
-- source:
--   The equivalence in Theorem 2.3 of C. Perassi, unpublished manuscript on Diaz's modulus conjecture (August 2026). The step (i) ⇒ (ii) is a direct instance of M. Waldschmidt, Solution du huitième problème de Schneider, J. Number Theory 5 (1973), 191–202, Cor. 4 (p. 192), at (mu, ū, v); the manuscript's route through D. Roy and M. Waldschmidt, Approximation diophantienne et indépendance algébrique de logarithmes, Ann. Sci. École Norm. Sup. (4) 30 (1997), 753–796, Th. 0.2, is not needed. Formal proof: Diaz modulus mission, 4 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem candidate_axis_ratio (u v : ℂ) (hu : IsCandidate u) (hv : IsCandidate v)
    (huv : u ≠ v) (hτ : (v - u).im = 0 ∨ (v - u).re = 0) :
    ((∃ m : ℚ, v * conj v = (m : ℂ) * (u * conj u)) ↔ ‖v‖ = ‖u‖) ∧
      (‖v‖ = ‖u‖ ↔ (((v - u).re = 0 → v = conj u) ∧ ((v - u).im = 0 → v = -conj u))) := by
  sorry

end DiazModulus
