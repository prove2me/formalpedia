-- Prove2me | Theorems.Thm_CKKSPrecision_FourierUnits_construction_rounding_bound
-- name    : CKKSPrecision.FourierUnits.construction_rounding_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:45:48.261801+00:00
-- url     : https://prove2.me/theorems/1fa2c166-b5e8-4067-aca8-c3d97be2e913
-- title:
--   Theorem 4.1 — construction and rounding bound
-- statement:
--   Let $r\ge2$ be a power of two, $m=4r$, and $t\in\mathbb R^r$ satisfy $\sum_jt_j=0$. Use $\sigma_j(\zeta)=\zeta^{5^j}$, $u_0=\zeta^{-2}c_5$ and $\ell_j=\log_2|\sigma_j(u_0)|$. Define $\widehat a_0=0$ and $\widehat a_k=\widehat t_k/\widehat\ell_k$ for $1\le k<r$, and take the normalized inverse Fourier transform. This inverse transform has zero imaginary part in every coordinate. Round its real coordinates to the nearest integers $n_j$, with the fixed half-integer tie rule toward $+\infty$, and form the actual product $u(n)=\prod_k\tau^{-k}(u_0)^{n_k}$. Then
--   $$
--   u(n)\in\mathbb Z[\zeta]^\times,
--   \qquad
--   \|\operatorname{Log}(u(n))-t\|_\infty\le C_r,
--   \qquad C_r=\frac12\sum_{j=0}^{r-1}|\ell_j|.
--   $$
--   This gives the specified unit for every real zero-sum target, without a bound on the target coordinates. The exact constant is the paper's displayed constant, depends only on the dimension through the fixed initial unit, and is independent of $t$.
--
--   **Formalization Note** The computed product is initially field valued; an equality with an actual unit of the integral coefficient ring asserts integral invertibility. The finite real function space has Mathlib's supremum norm.
--
--   Differences from the source:
--   - encoding: $K=\mathbb Q(\zeta)$ with the specified primitive complex root → Mathlib splitting field with the distinguished root sent to $\exp(2\pi i/m)$ by a fixed embedding; reason: an isomorphic model of the same field and root, with no additional hypothesis
--   - encoding: the inverse transform is a real vector $a\in\mathbb R^r$, as justified in the proof → compute the complex inverse transform, take real parts for rounding, and conclude that all imaginary parts vanish; reason: this retains the asserted reality as an obligation instead of an extra premise
--   - encoding: nearest-integer rounding with a fixed tie rule and integral-unit membership → $n_j=\lfloor a_j+1/2\rfloor$ and equality of the computed product with an element of $\mathbb Z[\zeta]^\times$; reason: ties toward positive infinity are an allowed fixed rule, and the unit witness asserts exactly invertibility in the integral ring
--   - encoding: a power-of-two integer dimension $r\ge2$ and real vectors in $\mathbb R^r$ with the infinity norm → a positive natural dimension with $r\ge2$, $r=2^q$ for some natural $q$, and functions `Fin r` to the reals with their supremum norm; reason: these encode exactly the same dimensions, coordinates and norm, without restricting target values
-- source:
--   Zhaoyang Liang, Runkun Liu, Jingwei Fang, Dan Ding, A New Approach to Reducing Modulus Requirements in Homomorphic Computation: Precision Allocation in CKKS, STOC 2027 submission #148 (October 2026), p. 8, Theorem 4.1; Eq. (8); Section 4.2 standing assumptions on p. 7 (PDF pp. 9–10)

import Definitions.Def_CKKSPrecision_FourierUnits_fourier_construction

set_option autoImplicit false

namespace CKKSPrecision.FourierUnits

theorem construction_rounding_bound (r : ℕ+) (hr : 2 ≤ (r : ℕ))
    (hp : ∃ q : ℕ, (r : ℕ) = 2 ^ q)
    (t : Fin (r : ℕ) → ℝ) (ht : t ∈ H (Fin (r : ℕ))) :
    (∀ j : Fin (r : ℕ), (inverseCoefficients r t j).im = 0) ∧
      (∃ u : (R (conductor r))ˣ,
        ((u : R (conductor r)) : K (conductor r)) = constructed r t) ∧
      ‖slotLog r (constructed r t) - t‖ ≤ roundingConstant r := by sorry

end CKKSPrecision.FourierUnits
