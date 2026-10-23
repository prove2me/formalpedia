-- Prove2me | Theorems.Thm_AKS_group_upper
-- name    : AKS.group_upper
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-10-21T12:53:24.197569+00:00
-- url     : https://prove2.me/theorems/807c19e4-250b-41cc-be9f-785cdb22bd45
-- title:
--   The Kalai-Sahai-Sudan collision bound for the group (Lemma 4.8)
-- statement:
--   Lemma 4.8 of the paper, whose proof is attributed to Kalai, Sahai, and Sudan: if n is not a power of p, then the group G-cal is small - at most n^(sqrt t). The proof: the bounded subset I-hat = {(n/p)^i p^j : i, j at most floor(sqrt t)} of I has (floor(sqrt t) + 1)^2 > t distinct numbers (distinct because a collision would force a power of p to equal a power of n, making n a power of p), so two of them, m1 > m2, are equal modulo r; then X^m1 = X^m2 modulo X^r - 1, and introspection turns the collision into the equation y^m1 = y^m2 satisfied by every image y in F of a polynomial of P, with m1 at most n^(floor(sqrt t)). So G-cal lies inside the root set of the polynomial Y^m1 - Y^m2, whose degree m1 is at most n^(sqrt t).
--
--   **Formalization Note** The statement is the collision: two numbers m2 < m1 at most n^(Nat.sqrt t), with every image of P in the field F_p[X]/(h) satisfying y^m1 = y^m2. The coprimality of n/p and p to r and the equality t = the size of the residue group G are hypotheses (they place the residues of I-hat inside G, by the order-divides-phi(r) window argument); the cardinality consequence - the root bound of Y^m1 - Y^m2 over a field gives at most m1 elements - is part of the goal's proposed work.
-- source:
--   M. Agrawal, N. Kayal, N. Saxena, PRIMES is in P, Ann. of Math. 160 (2004) 781-793, Section 4 (Lemma 4.8, proof by Kalai, Sahai, and Sudan).

import Mathlib
import Definitions.Def_AKS_poly
import Definitions.Def_AKS_alg

namespace AKS

/-!  Lemma 4.8 of the paper (Kalai, Sahai, and Sudan): if n is not a power
of p, the group G-cal lies in the roots of Y^(m_1) - Y^(m_2) for two
colliding elements m_2 < m_1 of the bounded set I-hat.  -/
theorem group_upper (n p r t ℓ : ℕ) [Fact (Nat.Prime p)]
    (h : Polynomial (ZMod p)) [Fact (Irreducible h)]
    (hdiv : h ∣ (Polynomial.X ^ r - 1 : Polynomial (ZMod p)))
    (hintros : ∀ m, inI n p m → ∀ f, inP p ℓ f → introspective p r f m)
    (hnpow : ¬ ∃ k, 0 < k ∧ n = p ^ k)
    (ht : t = (Gfin n p r).card)
    (hcop : Nat.gcd (n / p) r = 1 ∧ Nat.gcd p r = 1) :
    ∃ m₁ m₂ : ℕ, m₂ < m₁ ∧ m₁ ≤ n ^ (Nat.sqrt t) ∧
      ∀ f, inP p ℓ f →
        Polynomial.aeval (AdjoinRoot.root h) f ^ m₁
          = Polynomial.aeval (AdjoinRoot.root h) f ^ m₂ := by sorry

end AKS
