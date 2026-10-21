-- Prove2me | Theorems.Thm_BatchTesting_PTAS_card_FGreat_le
-- name    : BatchTesting.PTAS.card_FGreat_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:49:48.67298+00:00
-- url     : https://prove2.me/theorems/2d806444-e09c-4260-8149-60656d7c60fb
-- title:
--   §4.2, pp. 16–17 — $|F_{\mathrm{great}}|\le(n+1)(R+\lceil\log_{1+\epsilon}n\rceil+1)\binom{\lfloor3\kappa/\epsilon^2\rfloor+\kappa}{\kappa}$
-- statement:
--   Let $(p,c,\beta)$ be an instance with $n\ge1$, $p_i\in[0,1]$, $c_i>0$, $\beta\ge0$, let $0<\epsilon\le1$, and let $\kappa=\lceil\log_{1+\epsilon}(n/\epsilon)\rceil$ and $R$ the largest cost class. The number of great-looking states satisfies
--
--   $$|F_{\mathrm{great}}|\ \le\ (n+1)\cdot\big(R+\lceil\log_{1+\epsilon}n\rceil+1\big)\cdot\binom{\lfloor3\kappa/\epsilon^2\rfloor+\kappa}{\kappa}.$$
--
--   The three factors count the possible values of $\psi(N)$ (at most $n+1$: $-\infty$ or a non-empty class), of $\rho$, and of the vector $\mu$ with $\|\mu\|_1\le3\kappa/\epsilon^2$ on $\kappa$ middle classes; a great-looking state is determined by these parameters. The bound is $O((|I|/\epsilon)^{O(1/\epsilon^3)})$, which makes the dynamic program over $F_{\mathrm{great}}$ polynomial for fixed $\epsilon$.
--
--   **Formalization Note.** This is the explicit content of the three bullets on pp. 16–17; their $O(\cdot)$ conversions, and the running time itself, are not formalized.
-- source:
--   Segev & Shaposhnik, A Polynomial-Time Approximation Scheme for Sequential Batch Testing of Series Systems, SSRN preprint 3277805 (Nov. 2018), pp. 16–17, §4.2 (Bounding |F_great|)

import Mathlib
import Definitions.Def_BatchTesting_PTAS_Model

namespace BatchTesting.PTAS

theorem card_FGreat_le {n : ℕ} (I : Instance n) (hI : I.Standing) (eps : ℝ) (h0 : 0 < eps) (h1 : eps ≤ 1) :
    (FGreat I eps).card ≤ (n + 1) * (R I eps + ⌈Real.logb (1 + eps) (n : ℝ)⌉₊ + 1) *
      Nat.choose (⌊3 * (kappa n eps : ℝ) / eps ^ 2⌋₊ + (kappa n eps).toNat) (kappa n eps).toNat := by sorry

end BatchTesting.PTAS
