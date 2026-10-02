-- Prove2me | Theorems.Thm_DiazModulus_no_first_order_arithmetic_operator_unconditional
-- name    : DiazModulus.no_first_order_arithmetic_operator_unconditional
-- status  : Open
-- author  : @carlok
-- created : 2026-10-02T11:29:06.420935+00:00
-- url     : https://prove2.me/theorems/269d8402-b48a-4e0d-a58e-5aabc60e7293
-- title:
--   No first-order arithmetic differential operator for the exponential system of a candidate, unconditionally
-- statement:
--   Let $u$ be a candidate: $u \neq 0$ with $|u|$ and $e^{u}$ algebraic. Let $F(z, w) = \exp(uz + \bar u w)$, and let $X = a\,\partial_z + b\,\partial_w$ have polynomial coefficients $a, b$ with algebraic coefficients. If $(XF)(m, n)$ is algebraic at every lattice point $(m, n) \in \mathbb{Z}^2$, then $a = b = 0$.
--
--   This is `DiazModulus.no_first_order_arithmetic_operator` with its hypothesis, the linear independence of $1, u, \bar u$ over $\overline{\mathbb{Q}}$, discharged by `DiazModulus.candidate_qbar_independent_one_u_conj`.
--
--   **Proof.** `DiazModulus.no_first_order_arithmetic_operator u hu (DiazModulus.candidate_qbar_independent_one_u_conj u hu) a b ha hb hvalues`.
--
--   **Novelty.** Nothing beyond the parent node; its page gives the argument and the attribution.
-- source:
--   The statement and argument of `DiazModulus.no_first_order_arithmetic_operator` (Proposition 5.9 of the companion note, version 1.9), with its Baker hypothesis proved as `DiazModulus.candidate_qbar_independent_one_u_conj`. Formal proof: Diaz modulus mission, 2 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open ComplexConjugate

namespace DiazModulus

theorem no_first_order_arithmetic_operator_unconditional
    (u : ℂ) (hu : IsCandidate u)
    (a b : MvPolynomial (Fin 2) ℂ)
    (ha : ∀ d, IsAlgebraic ℚ (MvPolynomial.coeff d a))
    (hb : ∀ d, IsAlgebraic ℚ (MvPolynomial.coeff d b))
    (hvalues : ∀ m n : ℤ,
        IsAlgebraic ℚ
          ((MvPolynomial.eval (fun i : Fin 2 => if i = 0 then (m : ℂ) else (n : ℂ)) a * u
              + MvPolynomial.eval (fun i : Fin 2 => if i = 0 then (m : ℂ) else (n : ℂ)) b * conj u)
            * Complex.exp (u * m + conj u * n))) :
    a = 0 ∧ b = 0 := by
  sorry

end DiazModulus
