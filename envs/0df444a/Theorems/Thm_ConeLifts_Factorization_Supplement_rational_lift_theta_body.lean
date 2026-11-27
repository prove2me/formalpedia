-- Prove2me | Theorems.Thm_ConeLifts_Factorization_Supplement_rational_lift_theta_body
-- name    : ConeLifts.Factorization.Supplement.rational_lift_theta_body
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T10:52:31.591365+00:00
-- url     : https://prove2.me/theorems/91c160a9-bd4e-4544-9934-7073c0fe857e
-- title:
--   Theorem 5.6 (corrected: p ≠ 0 on ext(conv Z)) — rational psd lifts of varieties, sums of squares and theta bodies
-- statement:
--   Let $I \subseteq \mathbb R[x_1, \dots, x_n]$ be a convex radical ideal and $Z = \mathcal V_{\mathbb R}(I)$ its real zero set, such that $\operatorname{conv}(Z)$ is compact and contains the origin in its interior. Then:
--
--   1. for every polynomial $p$ with $p(x) \neq 0$ on $\operatorname{ext}(\operatorname{conv}(Z))$ and every vector $w = (w_1, \dots, w_k)$ of polynomials, the slack operator of $\operatorname{conv}(Z)$ has a rational factorization with $A(x) = \frac{1}{p(x)^2} w(x) w(x)^{\mathsf T} \in \mathcal S^k_+$ if and only if, for every linear polynomial $\ell$ nonnegative over $Z$, $p^2 \ell$ is a sum of squares modulo $I$ of polynomials that are linear combinations of $w_1, \dots, w_k$;
--   2. for every $k$, the slack operator of $\operatorname{conv}(Z)$ has a polynomial factorization $A(x) = w(x) w(x)^{\mathsf T}$ with every entry of $w$ of degree at most $k$ if and only if
--
--   $$
--   \mathrm{TH}_k(I) = \operatorname{conv}(Z).
--   $$
--
--   The theorem reads psd lifts of convex hulls of real varieties as sums-of-squares certificates, and identifies exactness of the $k$-th theta body with the existence of a degree-$k$ polynomial psd factorization.
--
--   **Formalization Note** A linear polynomial has total degree at most one. In part (2) the number of entries of $w$ is free.
--
--   Differences from the source:
--   - correction: $A(x) = \frac{1}{p(x)^2} w(x)w(x)^{\mathsf T}$ for all $x \in \operatorname{ext}(\operatorname{conv}(Z))$ → part (1) assumes $p(x) \neq 0$ on $\operatorname{ext}(\operatorname{conv}(Z))$; reason: the formula presupposes it; excluded are $p$ vanishing at an extreme point, where $A$ is undefined in the source
--   - reading: "contains the origin" → the origin is in the interior of $\operatorname{conv}(Z)$; reason: the standing convex-body assumption of p. 3, restated on pp. 21–22 as "contains the origin in its interior"
--   - reading: $v(x) = (v_1(x), \dots, v_n(x))$ and $\mathcal S^k_+$ in part (2) → $w$ has $k$ entries in part (1), and in part (2) the matrix size is free while $k$ bounds the degree; reason: $A(x) \in \mathcal S^k_+$ forces $k$ entries, and part (2) reuses the letter $k$ for the degree
-- source:
--   Gouveia, Parrilo & Thomas, Lifts of Convex Sets and Cone Factorizations, arXiv:1111.3164v2, p. 21, Theorem 5.6

import Mathlib
import Definitions.Def_ConeLifts_Factorization_IsConvexBody
import Definitions.Def_ConeLifts_Factorization_Supplement_IsConvexRadical
import Definitions.Def_ConeLifts_Factorization_Supplement_thetaBody
import Definitions.Def_ConeLifts_Factorization_Supplement_HasRationalFactorization

namespace ConeLifts.Factorization.Supplement

/-- **Theorem 5.6** of Gouveia, Parrilo & Thomas, arXiv:1111.3164v2, p. 21. Let `I` be a convex
radical ideal and `Z = 𝒱_ℝ(I)` with `conv(Z)` compact and containing the origin (in its interior,
the paper's standing convex-body assumption, restated on pp. 21–22). Then

1. the slack operator of `conv(Z)` has a rational factorization with
   `A(x) = (1/p(x)²) w(x) w(x)ᵀ ∈ Sᵏ₊` iff for every linear polynomial `ℓ` nonnegative over `Z`,
   `p² ℓ` is a sum of squares modulo `I` of linear combinations of the entries of `w`;
2. the slack operator of `conv(Z)` has a polynomial factorization `A(x) = w(x) w(x)ᵀ` with every
   entry of `w` of degree at most `k` iff `TH_k(I) = conv(Z)`.

Recorded repair in (1): `p(x) ≠ 0` for every `x ∈ ext(conv Z)`, which the form `1/p(x)²` of `A`
presupposes. In (2) the size `r` of the matrices is free; `k` is the degree bound. "Linear
polynomial" means total degree at most one. -/
theorem rational_lift_theta_body {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℝ))
    (hI : IsConvexRadical I)
    (hC : ConeLifts.Factorization.IsConvexBody (convexHull ℝ (realZeroSet I))) :
    (∀ (k : ℕ) (p : MvPolynomial (Fin n) ℝ) (w : Fin k → MvPolynomial (Fin n) ℝ),
      (∀ x ∈ Set.extremePoints ℝ (convexHull ℝ (realZeroSet I)), polyEval x p ≠ 0) →
      (HasRationalFactorization (convexHull ℝ (realZeroSet I)) p w ↔
        ∀ ℓ : MvPolynomial (Fin n) ℝ, ℓ.totalDegree ≤ 1 →
          (∀ z ∈ realZeroSet I, 0 ≤ polyEval z ℓ) →
            IsSosModulo I (Submodule.span ℝ (Set.range w) : Set (MvPolynomial (Fin n) ℝ))
              (p ^ 2 * ℓ))) ∧
    (∀ k : ℕ,
      (∃ (r : ℕ) (w : Fin r → MvPolynomial (Fin n) ℝ), (∀ i, (w i).totalDegree ≤ k) ∧
          HasRationalFactorization (convexHull ℝ (realZeroSet I)) 1 w) ↔
        thetaBody I k = convexHull ℝ (realZeroSet I)) := by sorry

end ConeLifts.Factorization.Supplement
