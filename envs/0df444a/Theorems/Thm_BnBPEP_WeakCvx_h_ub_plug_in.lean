-- Prove2me | Theorems.Thm_BnBPEP_WeakCvx_h_ub_plug_in
-- name    : BnBPEP.WeakCvx.h_ub_plug_in
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:46:00.885644+00:00
-- url     : https://prove2.me/theorems/f08f9cd5-575b-4849-9dd9-43af1944aa8d
-- title:
--   §6.3.3 — $h^\star_{\mathrm{ub}}=\sqrt{4\kappa^2(N+1)+1}/(2(N+1))$ minimizes (46), with value $\widetilde L^2(2\sqrt{4\kappa^2(N+1)+1}-1)/(N+1)$
-- statement:
--   Let $N\in\mathbb N$, $L>0$ and $\kappa\ge0$. For $h>0$ let
--   $$\varphi(h)=\frac{L^2}{N+1}\Big(-1+\frac{1}{2h}\Big(\frac{1}{N+1}+4\kappa^2\Big)+2h(N+1)\Big)$$
--   be the right-hand side of (46), and let
--   $$h^\star_{\mathrm{ub}}=\frac{\sqrt{4\kappa^2(N+1)+1}}{2(N+1)}.$$
--   Then
--
--   1. $\displaystyle \varphi(h^\star_{\mathrm{ub}})=\frac{L^2\big(2\sqrt{4\kappa^2(N+1)+1}-1\big)}{N+1}$;
--   2. $\varphi(h^\star_{\mathrm{ub}})\le\varphi(h)$ for every $h>0$, i.e. the minimum of (46) over $h>0$ is achieved at $h^\star_{\mathrm{ub}}$.
--
--   This produces the explicit stepsize and the explicit rate of Corollary 1.
--
--   **Formalization Note** $L$ is the paper's $\widetilde L$; $h^\star_{\mathrm{ub}}$ is written out inline in the Lean statement. Minimality is stated over all $h>0$, as on the page (not only over $h\in(0,\frac12]$).
-- source:
--   Das Gupta, Van Parys, Ryu, Branch-and-bound performance estimation programming, Math. Program. 204 (2024), §6.3.3, pp. 624–625, display after (46)

import Mathlib

namespace BnBPEP.WeakCvx

/-- §6.3.3, pp. 624–625: the right-hand side of (46),
`φ(h) = (L²/(N+1)) (-1 + (1/(2h))(1/(N+1) + 4κ²) + 2h(N+1))`, is minimized over `h > 0` at
`h⋆_ub = √(4κ²(N+1) + 1) / (2(N+1))`, where it equals `L² (2√(4κ²(N+1) + 1) - 1)/(N+1)`. -/
theorem h_ub_plug_in (N : ℕ) (L κ : ℝ) (hL : 0 < L) (hκ : 0 ≤ κ) :
    L ^ 2 / ((N : ℝ) + 1) * (-1
        + 1 / (2 * (√(4 * κ ^ 2 * ((N : ℝ) + 1) + 1) / (2 * ((N : ℝ) + 1))))
          * (1 / ((N : ℝ) + 1) + 4 * κ ^ 2)
        + 2 * (√(4 * κ ^ 2 * ((N : ℝ) + 1) + 1) / (2 * ((N : ℝ) + 1))) * ((N : ℝ) + 1))
      = L ^ 2 * (2 * √(4 * κ ^ 2 * ((N : ℝ) + 1) + 1) - 1) / ((N : ℝ) + 1) ∧
    ∀ h : ℝ, 0 < h →
      L ^ 2 / ((N : ℝ) + 1) * (-1
          + 1 / (2 * (√(4 * κ ^ 2 * ((N : ℝ) + 1) + 1) / (2 * ((N : ℝ) + 1))))
            * (1 / ((N : ℝ) + 1) + 4 * κ ^ 2)
          + 2 * (√(4 * κ ^ 2 * ((N : ℝ) + 1) + 1) / (2 * ((N : ℝ) + 1))) * ((N : ℝ) + 1))
        ≤ L ^ 2 / ((N : ℝ) + 1) * (-1 + 1 / (2 * h) * (1 / ((N : ℝ) + 1) + 4 * κ ^ 2)
          + 2 * h * ((N : ℝ) + 1)) := by sorry

end BnBPEP.WeakCvx
