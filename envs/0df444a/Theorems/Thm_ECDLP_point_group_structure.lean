-- Prove2me | Theorems.Thm_ECDLP_point_group_structure
-- name    : ECDLP.point_group_structure
-- status  : Open
-- author  : @Lucas
-- created : 2026-11-16T23:44:55.891949+00:00
-- url     : https://prove2.me/theorems/bd14d0fe-02b6-4ad9-a818-99856b095cdf
-- title:
--   Group structure of $E(\mathbb{F}_q)$: product of two cyclic groups
-- statement:
--   Let $E$ be an elliptic curve over a finite field $K$ with $q$ elements. Then the group of $K$-rational points is a product of two cyclic groups:
--
--   $$E(K) \cong \mathbb{Z}/n_1\mathbb{Z} \times \mathbb{Z}/n_2\mathbb{Z}$$
--
--   for some positive integers $n_1, n_2$ with $n_1 \mid n_2$ (and $n_1 n_2 = \#E(K)$). This classical structure theorem (Washington, Theorem 4.1) restricts the abstract group that can occur; for the challenge curve, with $\#E(\mathbb{F}_p) = 5n$ and $5 \nmid n$, it forces $E(\mathbb{F}_p)$ to be cyclic.
--
--   **Formalization Note.** The isomorphism is an `AddEquiv` (`≃+`) from the additive group `ZMod n₁ × ZMod n₂`; the `DecidableEq K` binder is required by Mathlib's chord-and-tangent `AddCommGroup` instance on points.
-- source:
--   Washington, Elliptic Curves: Number Theory and Cryptography, 2nd ed., Chapman & Hall/CRC 2008, Chapter 4, Theorem 4.1, https://doi.org/10.1201/9781420071474; Galbraith, Mathematics of Public Key Cryptography, Cambridge University Press 2012, Chapter 9, https://www.math.auckland.ac.nz/~sgal018/crypto-book/ch9.pdf.

import Mathlib

namespace ECDLP

theorem point_group_structure {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (E : WeierstrassCurve K) [E.IsElliptic] :
    ∃ n₁ n₂ : ℕ, 0 < n₁ ∧ 0 < n₂ ∧ n₁ ∣ n₂ ∧
      Nonempty (ZMod n₁ × ZMod n₂ ≃+ E.toAffine.Point) := by sorry

end ECDLP
