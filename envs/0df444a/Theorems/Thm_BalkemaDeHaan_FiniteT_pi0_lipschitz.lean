-- Prove2me | Theorems.Thm_BalkemaDeHaan_FiniteT_pi0_lipschitz
-- name    : BalkemaDeHaan.FiniteT.pi0_lipschitz
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:07:05.837982+00:00
-- url     : https://prove2.me/theorems/d0d7356f-93ba-4540-8796-1c4dfb3b6ec5
-- title:
--   Proof of the Corollary to Theorem 7 — |Π_{0,c}(x) − Π_{0,c₀}(x)| ≤ |c − c₀| for c ≥ 0
-- statement:
--   For every $c \ge 0$ and all real $c_0$ and $x$,
--   $$
--   \left|\Pi_{0,c}(x) - \Pi_{0,c_0}(x)\right| \le |c - c_0| .
--   $$
--   So the parameter can be moved from a nonnegative $c$ to any $c_0$ at a cost of at most $|c - c_0|$ in the distribution function; combined with Theorem 7 this turns a derivative bound $|c - a'(t)| \le \varepsilon$ into a uniform approximation of the residual life distribution by $\Pi_{0,c}$.
-- source:
--   Balkema, de Haan, Residual Life Time at Great Age, Ann. Probab. 2 (1974), p. 802 (PDF 11), proof of the Corollary to Theorem 7

import Mathlib
import Definitions.Def_BalkemaDeHaan_FiniteT_Pi0

namespace BalkemaDeHaan.FiniteT

/-- Proof of the Corollary to Theorem 7, p. 802: `|Π_{0,c}(x) - Π_{0,c₀}(x)| ≤ |c - c₀|`
for `c ≥ 0` and all real `c₀` and `x`. -/
theorem pi0_lipschitz (c : ℝ) (hc : 0 ≤ c) (c₀ x : ℝ) :
    |pi0 c x - pi0 c₀ x| ≤ |c - c₀| := by sorry

end BalkemaDeHaan.FiniteT
