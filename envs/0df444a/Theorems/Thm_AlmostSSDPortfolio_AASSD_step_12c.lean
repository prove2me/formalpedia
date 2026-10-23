-- Prove2me | Theorems.Thm_AlmostSSDPortfolio_AASSD_step_12c
-- name    : AlmostSSDPortfolio.AASSD.step_12c
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:31:04.322583+00:00
-- url     : https://prove2.me/theorems/d279e5e9-9241-4f04-9729-c1da827527e9
-- title:
--   Proof of Theorem 1, step (12c), p. 46 — the AASSD numerator equals 2∫_a^b (G^(2) − F^(2)_λ)
-- statement:
--   In the setting of §2, for a portfolio $\lambda\in\Lambda$ with return $X$ and the benchmark $Y$,
--   $$\mathrm{Var}(Y)+(b-\mathbb E Y)^2-\mathrm{Var}(X)-(b-\mathbb E X)^2=2\int_a^b\big(G^{(2)}(t)-F^{(2)}_\lambda(t)\big)\,dt.$$
--
--   This is the passage (12b)→(12c) of the proof of Theorem 1, which the paper derives from Lemma 1 applied to $Y$ and to $X$.
--
--   **Formalization Note.** The printed step rewrites the numerator of a ratio; the identity of numerators is its content and is stated directly. The hypothesis $\lambda\in\Lambda$ guarantees that the portfolio return lies in $[a,b]$.
-- source:
--   Luo, Chen & Jaillet, Portfolio Optimization Based on Almost Second-Degree Stochastic Dominance, accepted manuscript (April 2024) of Management Science doi:10.1287/mnsc.2022.01092, p. 46, proof of Theorem 1, (12b)–(12c)

import Mathlib
import Definitions.Def_AlmostSSDPortfolio_AASSD_Model
open MeasureTheory Set

namespace AlmostSSDPortfolio.AASSD

theorem step_12c {n T Tb : ℕ} (S : Setting n T Tb) (hS : S.Standing)
    (lam : Fin n → ℝ) (hlam : lam ∈ simplex n) :
    var S.q S.bv + (S.b - mean S.q S.bv) ^ 2 - var S.p (S.ret lam) -
        (S.b - mean S.p (S.ret lam)) ^ 2
      = 2 * ∫ t in S.a..S.b, (S.G2 t - S.F2 lam t) := by sorry

end AlmostSSDPortfolio.AASSD
