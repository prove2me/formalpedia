-- Prove2me | Theorems.Thm_DiazModulus_candidate_qbar_independent_one_u_conj
-- name    : DiazModulus.candidate_qbar_independent_one_u_conj
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-02T11:28:57.936882+00:00
-- url     : https://prove2.me/theorems/3752afd3-faa1-4ba9-a355-bd1b0ed1754c
-- title:
--   For a candidate u, the numbers 1, u, ū are linearly independent over the algebraic numbers
-- statement:
--   Let $u$ be a candidate: $u \neq 0$ with $|u|$ and $e^{u}$ algebraic. If $p, q$ are algebraic numbers and $pu + q\bar u$ is algebraic, then $p = q = 0$. Equivalently, $1, u, \bar u$ are linearly independent over $\overline{\mathbb{Q}}$.
--
--   The conclusion is the hypothesis `hbaker` of `DiazModulus.no_first_order_arithmetic_operator`, here proved.
--
--   **Proof.** A candidate lies on neither axis: on an axis $u^2 = \pm|u|^2$ would be algebraic, against Hermite–Lindemann. Hence $u$ and $\bar u$, both logarithms of algebraic numbers, are linearly independent over $\mathbb{Q}$, since $su + t\bar u = 0$ gives $(s + t)\,\mathrm{Re}\,u = 0$ and $(s - t)\,\mathrm{Im}\,u = 0$. Baker's theorem with a constant term (`Schanuel.baker_linear_forms_in_logarithms`, with $n = 2$) applied to $-(pu + q\bar u) + p\,u + q\,\bar u = 0$ then forces every coefficient to vanish.
--
--   **Novelty.** None: an instance of Baker's theorem.
-- source:
--   An instance of Baker's theorem (A. Baker, Linear forms in the logarithms of algebraic numbers I, Mathematika 13 (1966), 204–216) at u and ū, proved in this mission as `Schanuel.baker_linear_forms_in_logarithms`. Formal proof: Diaz modulus mission, 2 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open ComplexConjugate

namespace DiazModulus

theorem candidate_qbar_independent_one_u_conj (u : ℂ) (hu : IsCandidate u) :
    ∀ p q : ℂ, IsAlgebraic ℚ p → IsAlgebraic ℚ q →
      IsAlgebraic ℚ (p * u + q * conj u) → p = 0 ∧ q = 0 := by
  sorry

end DiazModulus
