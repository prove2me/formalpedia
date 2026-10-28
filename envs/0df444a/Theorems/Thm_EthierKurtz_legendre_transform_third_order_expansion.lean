-- Prove2me | Theorems.Thm_EthierKurtz_legendre_transform_third_order_expansion
-- name    : EthierKurtz.legendre_transform_third_order_expansion
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-27T00:22:16.110494+00:00
-- url     : https://prove2.me/theorems/ac2ce293-d7a8-43b5-bb49-7920afd8b316
-- title:
--   Third-order expansion of a Legendre transform
-- statement:
--   Let $L,L_1,L_2:\mathbb R\to\mathbb R$ and $t,t',B,R\in\mathbb R$ with $L_2(t)\ge\tfrac12$, $|t'-t|\le2|L_1(t')-L_1(t)|$, $B\ge0$, $|L_1(t')-L_1(t)|\le R$,
--
--   $$|L_1(t')-L_1(t)-L_2(t)(t'-t)|\le\tfrac B2|t'-t|^2,\qquad\big|L(t')-L(t)-L_1(t)(t'-t)-\tfrac12L_2(t)(t'-t)^2\big|\le\tfrac B6|t'-t|^3.$$
--
--   Then with $\Delta=L_1(t')-L_1(t)$
--
--   $$\Big|t'L_1(t')-L(t')-\big(tL_1(t)-L(t)\big)-t\Delta-\frac{\Delta^2}{2L_2(t)}\Big|\le(4B^2R+2B)|\Delta|^3.$$
--
--   Role: The expansion of the Legendre transform $\Lambda^*(x)=tx-\Lambda(t)$, $x=\Lambda'(t)$, used 'in the usual way' to pass from the saddle-point formula to Lemma 2 (b).
-- source:
--   J. Komlós, P. Major, G. Tusnády, An approximation of partial sums of independent RV's and the sample DF. II, Z. Wahrsch. verw. Gebiete 34 (1976) 33-58, https://static.renyi.hu/~major/articles/KMT2.pdf, proof of Lemma 2, p. 40 (choosing t as the solution of x = psi'(t) gives (b) 'in the usual way'); V. V. Petrov, Sums of Independent Random Variables, Springer 1975, Ch. VIII, §2

import Mathlib

namespace EthierKurtz

theorem legendre_transform_third_order_expansion :
    ∀ (L L1 L2 : ℝ → ℝ) {t t' B R : ℝ},
      (1 / 2 : ℝ) ≤ L2 t →
        |t' - t| ≤ (2 : ℝ) * |L1 t' - L1 t| →
          (0 : ℝ) ≤ B →
            |L1 t' - L1 t| ≤ R →
              |L1 t' - L1 t - L2 t * (t' - t)| ≤ B * |t' - t| ^ (2 : ℕ) / (2 : ℝ) →
                |L t' - L t - L1 t * (t' - t) - L2 t * (t' - t) ^ (2 : ℕ) / (2 : ℝ)| ≤ B * |t' - t| ^ (3 : ℕ) / (6 : ℝ) →
                  |t' * L1 t' - L t' - (t * L1 t - L t) - t * (L1 t' - L1 t) -
                        (L1 t' - L1 t) ^ (2 : ℕ) / ((2 : ℝ) * L2 t)| ≤
                    ((4 : ℝ) * B ^ (2 : ℕ) * R + (2 : ℝ) * B) * |L1 t' - L1 t| ^ (3 : ℕ) := by sorry

end EthierKurtz
