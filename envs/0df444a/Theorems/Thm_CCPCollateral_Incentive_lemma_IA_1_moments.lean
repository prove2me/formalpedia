-- Prove2me | Theorems.Thm_CCPCollateral_Incentive_lemma_IA_1_moments
-- name    : CCPCollateral.Incentive.lemma_IA_1_moments
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:22:10.111325+00:00
-- url     : https://prove2.me/theorems/b283e136-b4b7-4a35-ba64-e57cf911fbde
-- title:
--   Lemma IA.1 (last sentence), p. OA-1 — E^s, E^r of N_d/(N − N_d) and N/(N − N_d)
-- statement:
--   Under the standing assumptions, let $\mathbb E^s$ denote expectation under the law $f^{N-1}$ of the number $\mathcal N_d$ of defaults among the other $N-1$ members when all of them hedge (so $\mathcal N_d\sim\mathrm{Bin}(N-1,q_s)$), and $\mathbb E^r$ expectation under $f^{0}$ (none hedges, $\mathcal N_d\sim\mathrm{Bin}(N-1,q_r)$). Then
--   $$\mathbb E^s\!\left[\frac{\mathcal N_d}{N-\mathcal N_d}\right]=\frac{q_s-q_s^N}{1-q_s},\qquad \mathbb E^s\!\left[\frac{N}{N-\mathcal N_d}\right]=\frac{1-q_s^N}{1-q_s},$$
--   $$\mathbb E^r\!\left[\frac{\mathcal N_d}{N-\mathcal N_d}\right]=\frac{q_r-q_r^N}{1-q_r},\qquad \mathbb E^r\!\left[\frac{N}{N-\mathcal N_d}\right]=\frac{1-q_r^N}{1-q_r}.$$
--
--   These closed forms turn the derivative formula (A7) and the explicit cutoffs (A15)–(A17) into expressions in $q_s$ alone.
--
--   **Formalization Note** Each expectation is the finite sum $\sum_{k=0}^{N-1}f^g(k)\,\varphi(k)$ with $g=N-1$ or $g=0$.
-- source:
--   Wang, Capponi & Zhang, A Theory of Collateral Requirements for Central Counterparties, author's manuscript (2021; Management Sci. doi:10.1287/mnsc.2021.4145), Online Appendix, Lemma IA.1, last sentence, p. OA-1

import Mathlib
import Definitions.Def_CCPCollateral_Incentive_Setting

namespace CCPCollateral.Incentive

/-- Lemma IA.1 (p. OA-1), last sentence: under `E^s` (law `f^{N−1}`) and `E^r` (law `f^0`) of the
number `k` of defaults among the other `N − 1` members,
`E^s[k/(N−k)] = (q_s − q_s^N)/(1 − q_s)`, `E^s[N/(N−k)] = (1 − q_s^N)/(1 − q_s)`,
`E^r[k/(N−k)] = (q_r − q_r^N)/(1 − q_r)`, `E^r[N/(N−k)] = (1 − q_r^N)/(1 − q_r)`. -/
theorem lemma_IA_1_moments (m : Params) (hm : Standing m) :
    ∑ k ∈ Finset.range m.N, m.defaultLaw (m.N - 1) k * ((k : ℝ) / ((m.N : ℝ) - k)) =
        (m.qs - m.qs ^ m.N) / (1 - m.qs) ∧
    ∑ k ∈ Finset.range m.N, m.defaultLaw (m.N - 1) k * ((m.N : ℝ) / ((m.N : ℝ) - k)) =
        (1 - m.qs ^ m.N) / (1 - m.qs) ∧
    ∑ k ∈ Finset.range m.N, m.defaultLaw 0 k * ((k : ℝ) / ((m.N : ℝ) - k)) =
        (m.qr - m.qr ^ m.N) / (1 - m.qr) ∧
    ∑ k ∈ Finset.range m.N, m.defaultLaw 0 k * ((m.N : ℝ) / ((m.N : ℝ) - k)) =
        (1 - m.qr ^ m.N) / (1 - m.qr) := by sorry

end CCPCollateral.Incentive
