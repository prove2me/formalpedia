-- Prove2me | Theorems.Thm_Apery_growth_mN
-- name    : Apery.growth_mN
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-12T14:20:53.317575+00:00
-- url     : https://prove2.me/theorems/bbf7a6e3-35e0-481a-a0c6-913f9929e8ae
-- title:
--   Proposition 5.2 (as used) — growth of the normaliser
-- statement:
--   For every $\varepsilon > 0$, for all large $n$,
--
--   $$\log m_K \;\le\; (A_{\mathrm{eff}} + \varepsilon)\,K^2, \qquad K = 40n,\quad A_{\mathrm{eff}} = \frac{136}{100},$$
--
--   where $m_K = \prod_{p \le 2h} p^{-L_p}$ is the normaliser of `Apery/Norm.lean`. This is the form of Proposition 5.2 proved in the source (module `Apery/Growth.lean`, theorem `growth_mN`). The source assembles four prime ranges: small primes $p \le K/400$ contribute $22.2/1600 \cdot K^2 = 0.013875 K^2$; the tail $K/400 < p \le K/20$ contributes at most $-6843153/128000000 \cdot K^2 \approx -0.05346K^2$; the exact table (5.18) over $K/20 < p \le K/3$ contributes $322437603634266857629/7535670527041937280000 \cdot K^2 \approx 0.04279 K^2$; the outer table over $K/3 < p \le 2h$ contributes $129101/96000 \cdot K^2 \approx 1.34480 K^2$; the total $1.3480 K^2 < A_{\mathrm{eff}}K^2$ leaves room for the $o(K^2)$ errors. **Formalization Note** The statement is the source's; the constant $A_{\mathrm{eff}}$ is weaker than the paper's $A_{200}$ but below $-U$, which suffices for the irrationality criterion. In the source the small-prime range uses the prime number theorem, imported there from the external package `PrimeNumberTheoremAnd`.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Growth.lean#L72-L123 (Proposition 5.2)

import Mathlib
import Definitions.Def_Zeta5_SourceNorm
import Definitions.Def_Zeta5_SourceConstants

open Filter

namespace Apery

theorem growth_mN :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, Real.log (mN n) ≤ ((Aeff : ℝ) + ε) * Kr n ^ 2 := by
  sorry

end Apery
