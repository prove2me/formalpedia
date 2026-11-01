-- Prove2me | Theorems.Thm_BayesBAI_lemma_12
-- name    : BayesBAI.lemma_12
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:53:38.456576+00:00
-- url     : https://prove2.me/theorems/7245d063-f9f3-4371-9a97-e042ce853780
-- title:
--   Lemma 12 — symmetry of $d_{\mathrm{KL}}$ (corrected: exponent $1/3$ in (14))
-- statement:
--   There is a universal constant $C_{\mathrm{KL}}>0$ such that, in the setting of Appendix C, with $m=(l+u)/2$,
--   $$
--   |d_{\mathrm{KL}}(m,u)-d_{\mathrm{KL}}(l,m)|\le C_{\mathrm{KL}}\,h^3\,T^{1/3},\tag{13}
--   $$
--   $$
--   |d_{\mathrm{KL}}(m,u)-d_{\mathrm{KL}}(u,m)|\le C_{\mathrm{KL}}\,h^3\,T^{1/3}.\tag{14}
--   $$
--   These compare the divergences of the half-gaps, which is the step from Lemma 11 to the midpoint form of Lemma 13.
--
--   Differences from the source:
--   - correction: |d_KL(m,u) − d_KL(u,m)| ≤ C_KL h³ T^(1/6) in (14) → exponent 1/3; reason: the printed exponent is false: at l = T^(−1/6), u = l + 0.99h, h = √(log T/T), the ratio |d_KL(m,u) − d_KL(u,m)|/(h³T^(1/6)) is 0.19, 2.02, 202, 2.0·10⁶ at T = 10⁶, 10¹², 10²⁴, 10⁴⁸ and unbounded, while with T^(1/3) it is stable at 0.020 (Reading 7)
--   - encoding: h(T) = o(T^(−1/6)) and a threshold T₀ with 2h(T) < T^(−1/6), T^(−1/6) < 1/2 for T ≥ T₀ → the same inequalities at one real T, as KLSetting T l u h; reason: this gives the printed statement for every such h, T₀, and shows the constants are universal
-- source:
--   Komiyama, Ariu, Kato, Qin, Rate-optimal Bayesian Simple Regret in Best Arm Identification, arXiv:2111.09885v3, Lemma 12, eqs. (13), (14), p.18

import Mathlib
import Definitions.Def_BayesBAI_KLSetting
import Definitions.Def_RegretBandits_Stochastic_klBernoulli

namespace BayesBAI

open RegretBandits.Stochastic in
/-- Lemma 12, Komiyama, Ariu, Kato, Qin, arXiv:2111.09885v3, p.18, with the exponent of (14)
corrected: for a universal `C_KL > 0`, in the setting of p.17 with `m = (l + u)/2`,
(13) `|d_KL(m, u) - d_KL(l, m)| ≤ C_KL h³ T^(1/3)` and
(14) `|d_KL(m, u) - d_KL(u, m)| ≤ C_KL h³ T^(1/3)`.

**Formalization Note.** The page prints `T^(1/6)` in (14). That is false: take `l = T^(-1/6)`,
`u = l + 0.99 h`, `h = √(log T / T)`; then `|d_KL(m, u) - d_KL(u, m)| / (h³ T^(1/6))` is unbounded (it is
`2.0·10⁶` at `T = 10⁴⁸`), while with `T^(1/3)` the ratio is stable. `∃ C` comes before all the data. -/
theorem lemma_12 :
    ∃ C : ℝ, 0 < C ∧ ∀ {T l u h : ℝ}, KLSetting T l u h →
      |klBern ((l + u) / 2) u - klBern l ((l + u) / 2)| ≤ C * h ^ 3 * T ^ ((1 : ℝ) / 3) ∧
      |klBern ((l + u) / 2) u - klBern u ((l + u) / 2)| ≤ C * h ^ 3 * T ^ ((1 : ℝ) / 3) := by sorry

end BayesBAI
