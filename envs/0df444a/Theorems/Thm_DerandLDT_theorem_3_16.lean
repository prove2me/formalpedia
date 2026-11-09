-- Prove2me | Theorems.Thm_DerandLDT_theorem_3_16
-- name    : DerandLDT.theorem_3_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T23:06:44.130218+00:00
-- url     : https://prove2.me/theorems/57adc8ba-257b-4ed0-b563-04d16559b7da
-- title:
--   Theorem 3.16 — explicit Newton iteration [Fur67, BKRRSS26] (corrected: $+\,a$)
-- statement:
--   Let $K$ be a field, $P(Y, Z) \in K[Y, Z]$ and $a \in K$ with $P(0, a) = 0$ and $\alpha = \partial_Z(P)(0, a) \neq 0$, and let $\Phi_k$ be the Newton approximations of Theorem 3.15. Then for every $k \ge 1$,
--   $$
--   \Phi_k(Y) = \left( a + \sum_{m=1}^{2k} \frac{1}{\alpha^{m+1}} \, [Z^{m-1}] \Big\{ \partial_Z\big(P(Y, Z + a)\big) \cdot \big(\alpha Z - P(Y, Z + a)\big)^m \Big\} \right) \bmod Y^{k+1},
--   $$
--   where $[Z^{j}]\{\cdot\}$ is the coefficient of $Z^j$, a polynomial in $Y$.
--
--   The closed form shows that the denominators of the lifted root in Lemma 4.1 are powers of $\alpha$ and bounds the degree growth (Claim 4.3).
--
--   **Formalization Note** $P$ is a polynomial in $Z$ with coefficients in $K[Y]$; $P(Y, Z + a)$ is the composition with $Z + a$; $\Phi_k$ is `DerandLDT.newtonApprox P a k`.
--
--   Differences from the source:
--   - correction: Φ_k equals (∑_{m=1}^{2k} α^{-(m+1)} [Z^{m−1}]{…}) mod Y^{k+1} → Φ_k equals (a + ∑_{m=1}^{2k} α^{-(m+1)} [Z^{m−1}]{…}) mod Y^{k+1}; reason: the printed sum omits the constant term: for K = ℚ, P = Z − 1 − Y, a = 1 (α = 1), Φ₁ = 1 + Y while the printed sum is [Z⁰]{Y} + [Z¹]{Y²} = Y (checked in Lean)
--   - generalization: P ∈ F[Y, Z] for a subfield F of K → P ∈ K[Y, Z]; reason: F[Y, Z] ⊆ K[Y, Z], so the paper's case is an instance
-- source:
--   Harsha–Kopparty–Kumar–Saptharishi–Sudan, On derandomizing the line-point low-degree test, STOC 2027 submission (manuscript sha256 d57e7d6f…80df), Theorem 3.16, p.14

import Definitions.Def_DerandLDT_newtonApprox

set_option autoImplicit false

universe u

namespace DerandLDT

open Polynomial

/-- **Theorem 3.16** (explicit Newton iteration [Fur67, BKRRSS26]), corrected. Harsha, Kopparty, Kumar, Saptharishi, Sudan, *On derandomizing the line-point
low-degree test*, STOC 2027 submission manuscript (sha256 d57e7d6f…80df),
Theorem 3.16, p.14: *With `F, K, P, a` and `Φ_k` as in Theorem 3.15 and `α = ∂_Z(P)(0, a)`,
`Φ_k(Y)` equals
`(∑_{m=1}^{2k} (1/α^{m+1}) [Z^{m-1}]{∂_Z(P(Y, Z + a)) · (αZ − P(Y, Z + a))^m}) mod Y^{k+1}`.*

**Formalization Note.** The printed right-hand side omits the constant term `a`: for
`K = ℚ`, `P = Z − 1 − Y`, `a = 1` (so `α = 1`) one has `Φ₁ = 1 + Y`, while the printed sum is
`[Z⁰]{Y} + [Z¹]{Y²} = Y`. The corrected right-hand side is `(a + ∑ …) mod Y^{k+1}`. `P : K[X][X]`
is a polynomial in `Z` (outer) with coefficients in `K[Y]`; `P(Y, Z + a)` is
`P.comp (X + C (C a))`, `[Z^{m-1}]{·}` is `coeff (m - 1)`, and `Φ_k` is `newtonApprox P a k`.
The statement is made for every `P` with coefficients in `K`. -/
theorem theorem_3_16 (K : Type u) [Field K] (P : K[X][X]) (a : K)
    (h0 : (P.eval (C a)).eval 0 = 0) (h1 : ((derivative P).eval (C a)).eval 0 ≠ 0)
    (k : ℕ) (hk : 1 ≤ k) :
    newtonApprox P a k =
      (C a + ∑ m ∈ Finset.Icc 1 (2 * k),
          C ((((derivative P).eval (C a)).eval 0) ^ (m + 1))⁻¹ *
            (derivative (P.comp (X + C (C a))) *
              (C (C (((derivative P).eval (C a)).eval 0)) * X - P.comp (X + C (C a))) ^ m).coeff
              (m - 1)) %ₘ (X : K[X]) ^ (k + 1) := by sorry

end DerandLDT
