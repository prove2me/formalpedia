-- Prove2me | Theorems.Thm_DynamicOnlineLP_DLA_expected_partialOPT_le
-- name    : DynamicOnlineLP.DLA.expected_partialOPT_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T19:45:32.833631+00:00
-- url     : https://prove2.me/theorems/9f0873e2-ea09-45db-9d19-349dd2e6d4ef
-- title:
--   Lemma 7 — E[OPT_ℓ((ℓ/n) b)] ≤ (ℓ/n) OPT
-- statement:
--   Let an online LP instance have $n$ columns ($\pi_t\ge0$, $a_t\in[0,1]^m$) and right-hand side $b\ge0$, arriving in a uniformly random order, and let $\mathrm{OPT}$ be the optimal value of the offline program (1). For $\ell\in\{0,\dots,n\}$ let $\mathrm{OPT}_\ell(d)$ be the optimal value of the partial program on the first $\ell$ arrivals with right-hand side $d$. Then
--
--   $$\mathbb E\Big[\mathrm{OPT}_\ell\Big(\frac{\ell}{n}\,b\Big)\Big]\le\frac{\ell}{n}\,\mathrm{OPT},$$
--
--   the expectation being over the random arrival order.
--
--   The lemma bounds the value that is lost by not accepting anything in the learning periods: a random sample of $\ell$ columns with a proportionally scaled budget is worth, in expectation, at most its proportional share of the offline optimum.
--
--   **Formalization Note** The expectation is the average over all $n!$ permutations. The paper's "for any $\ell$" is read as $0\le\ell\le n$ (the first $\ell$ arrivals must exist). The hypothesis $b\ge0$ makes both programs feasible, so that both optimal values are true optima.
-- source:
--   Agrawal, Wang, Ye, A Dynamic Near-Optimal Algorithm for Online Linear Programming, Oper. Res. 62(4), 2014, p. 884, Lemma 7 (proof as for Lemma 4, p. 883)

import Mathlib
import Definitions.Def_DynamicOnlineLP_DLA_PackingLP
import Definitions.Def_DynamicOnlineLP_DLA_Instance

namespace DynamicOnlineLP.DLA

/-- Lemma 7 (Agrawal–Wang–Ye 2014, p. 884): for any `ℓ`, the expected optimal value of the partial
LP on the first `ℓ` arrivals with right-hand side `(ℓ/n) b` is at most `(ℓ/n) OPT`; the expectation
is over a uniformly random arrival order. -/
theorem expected_partialOPT_le {m n : ℕ} (I : Instance m n) (hb : ∀ i : Fin m, 0 ≤ I.b i)
    (ℓ : ℕ) (hℓ : ℓ ≤ n) :
    avgPerm (fun σ : Equiv.Perm (Fin n) =>
        I.partialOPT σ ℓ (fun i => ((ℓ : ℝ) / (n : ℝ)) * I.b i)) ≤
      ((ℓ : ℝ) / (n : ℝ)) * I.OPT := by sorry

end DynamicOnlineLP.DLA
