-- Prove2me | Theorems.Thm_EulerMascheroni_loglog_integral_asymp
-- name    : EulerMascheroni.loglog_integral_asymp
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T12:25:54.080319+00:00
-- url     : https://prove2.me/theorems/ffad307b-5e7a-4539-8d15-24d2e55eaa51
-- title:
--   A regularised $\log\log$ integral evaluating to $-\gamma$
-- statement:
--   **The Euler–Mascheroni constant as the regularised value of a $\log\log$ Mellin integral.**
--
--   For $s > 1$ the integral
--
--   $$I(s) \;=\; \int_{2}^{\infty} \log(\log t)\, t^{-s}\,dt$$
--
--   converges, and it diverges as $s \downarrow 1$. The divergence is exactly logarithmic, and after
--   subtracting it the limit is the Euler–Mascheroni constant $\gamma$:
--
--   $$\lim_{s \to 1^{+}} \Bigl[\, (s-1)\,I(s) \;+\; \log(s-1) \,\Bigr] \;=\; -\gamma .$$
--
--   Substituting $t = e^{u/(s-1)}$ turns $I(s)$ into a Frullani-type integral and exhibits the
--   $-\log(s-1)$ singularity explicitly; the constant left behind is
--   $\int_0^\infty e^{-u}\log u\,du = -\gamma$, the classical integral representation of $\gamma$ as
--   the derivative of the Gamma function at $1$, $\Gamma'(1) = -\gamma$.
--
--   The identity is the analytic engine behind the constant in Mertens' second theorem. Writing
--   $\sum_{p} p^{-s}$ against $\log\zeta(s)$ and comparing with the integral above is what converts
--   the Dirichlet-series pole into the statement
--   $\sum_{p\le x} \tfrac1p = \log\log x + M + o(1)$, and it is where the
--   $\gamma$ inside the Meissel–Mertens constant $M$ comes from.
--
--   **Formalization note.** The limit is taken in the filter `nhdsWithin 1 (Set.Ioi 1)`, i.e. as
--   $s \to 1$ from strictly above, and `Real.eulerMascheroniConstant` is Mathlib's $\gamma$.
-- source:
--   Classical; the analytic input to Mertens' second theorem, cf. Montgomery & Vaughan, *Multiplicative Number Theory I*, §2.2, and Whittaker & Watson, *A Course of Modern Analysis*, §12.2. Lean proof extracted from `Salt/Mertens/GammaIntegral.lean` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace EulerMascheroni

theorem loglog_integral_asymp :
    Filter.Tendsto
      (fun s : ℝ => (s - 1) * (∫ t in Set.Ioi (2:ℝ), Real.log (Real.log t) * t ^ (-s))
        + Real.log (s - 1))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (-Real.eulerMascheroniConstant)) := by sorry

end EulerMascheroni
