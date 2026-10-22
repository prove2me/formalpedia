-- Prove2me | Theorems.Thm_DynamicOnlineLP_DLA_phase_sums
-- name    : DynamicOnlineLP.DLA.phase_sums
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T19:50:10.527367+00:00
-- url     : https://prove2.me/theorems/ff1869e6-b6af-4657-89a4-76a7918e05b5
-- title:
--   §3.1, proof of Theorem 1, final display — Σ_{ℓ∈L} ℓ/n = 1 − ε and Σ_{ℓ∈L} h_ℓ ℓ/n = ε Σ_{ℓ∈L} √(ℓ/n) ≤ 2.5ε
-- statement:
--   Let $\varepsilon=2^{-E}$ with $E\ge1$, let $n\ge1$ with $\varepsilon n$ an integer, and let $L=\{\varepsilon n,2\varepsilon n,\dots,2^{E-1}\varepsilon n\}$ and $h_\ell=\varepsilon\sqrt{n/\ell}$. Then
--
--   $$\sum_{\ell\in L}\frac{\ell}{n}=1-\varepsilon,\qquad \sum_{\ell\in L}h_\ell\,\frac{\ell}{n}=\varepsilon\sum_{\ell\in L}\sqrt{\frac{\ell}{n}}\le 2.5\,\varepsilon.$$
--
--   These are the two summations with which the paper closes the proof of Theorem 1: the doubling periods cover all but an $\varepsilon$ fraction of the horizon, and the total slack $h_\ell$ weighted by period length is $O(\varepsilon)$.
-- source:
--   Agrawal, Wang, Ye, A Dynamic Near-Optimal Algorithm for Online Linear Programming, Oper. Res. 62(4), 2014, p. 885, §3.1, proof of Theorem 1, final display

import Mathlib
import Definitions.Def_DynamicOnlineLP_DLA_Algorithm

namespace DynamicOnlineLP.DLA

/-- Agrawal–Wang–Ye 2014, §3.1, proof of Theorem 1, final display (p. 885): with `ε = 2^{-E}` and
`L = {εn, 2εn, …, 2^{E−1}εn}`,
`∑_{ℓ∈L} ℓ/n = 1 - ε` and `∑_{ℓ∈L} h_ℓ ℓ/n = ε ∑_{ℓ∈L} √(ℓ/n) ≤ 2.5 ε`. -/
theorem phase_sums (n E : ℕ) (hn : 0 < n) (hE : 1 ≤ E) (hdiv : 2 ^ E ∣ n) :
    ∑ ℓ ∈ phases n E, (ℓ : ℝ) / (n : ℝ) = 1 - eps E ∧
      ∑ ℓ ∈ phases n E, slack n E ℓ * ((ℓ : ℝ) / (n : ℝ)) =
        eps E * ∑ ℓ ∈ phases n E, Real.sqrt ((ℓ : ℝ) / (n : ℝ)) ∧
      eps E * ∑ ℓ ∈ phases n E, Real.sqrt ((ℓ : ℝ) / (n : ℝ)) ≤ 2.5 * eps E := by sorry

end DynamicOnlineLP.DLA
