-- Prove2me | Theorems.Thm_BayesBAI_lemma_13
-- name    : BayesBAI.lemma_13
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:53:38.495224+00:00
-- url     : https://prove2.me/theorems/c2472d0e-e296-4e91-b278-bfff10f20f35
-- title:
--   Lemma 13 — $d_{\mathrm{KL}}$ around the midpoint, relative form
-- statement:
--   Let $C_h>0$ and $h(T)=\sqrt{C_h\log T/T}$. There are $C_a>0$ and $T_0$ such that for all $T\ge T_0$ and all $l,u$ in the setting of Appendix C, with $m=(l+u)/2$, $A=\frac{(u-l)^2}{2m(1-m)}$ and $e=C_aT^{-1/3}\sqrt{\log T}$:
--
--   1. $|d_{\mathrm{KL}}(l,u)-A|\le eA$ and $|d_{\mathrm{KL}}(u,l)-A|\le eA$;
--   2. each of $d_{\mathrm{KL}}(m,u)$, $d_{\mathrm{KL}}(u,m)$, $d_{\mathrm{KL}}(m,l)$, $d_{\mathrm{KL}}(l,m)$ is within $eA/4$ of $A/4$.
--
--   So all these divergences are given by the midpoint variance up to a vanishing relative error, which is the accuracy that Lemma 15 uses.
--
--   Differences from the source:
--   - generalization: additive error C_a T^(−1/6)(log T)³ around (u−l)²/(2m(1−m)) and (u−l)²/(8m(1−m)) → relative error C_a T^(−1/3)√(log T) times the main term A, A/4; reason: implies the printed form, as A ≤ 1 and T^(−1/3)√(log T) ≤ T^(−1/6)(log T)³ for large T; the printed additive error dwarfs the main term of order (log T)/T, so Lemma 15 needs this form (Reading 8)
--   - encoding: h(T) = o(T^(−1/6)) and a threshold T₀ with 2h(T) < T^(−1/6), T^(−1/6) < 1/2 for T ≥ T₀ → the same inequalities at one real T, as KLSetting T l u h; reason: this gives the printed statement for every such h, T₀, and shows the constants are universal
-- source:
--   Komiyama, Ariu, Kato, Qin, Rate-optimal Bayesian Simple Regret in Best Arm Identification, arXiv:2111.09885v3, Lemma 13, p.19

import Mathlib
import Definitions.Def_BayesBAI_KLSetting
import Definitions.Def_RegretBandits_Stochastic_klBernoulli

namespace BayesBAI

open RegretBandits.Stochastic in
/-- Lemma 13 (bound on the KL divergence), Komiyama, Ariu, Kato, Qin, arXiv:2111.09885v3, p.19, in
relative form: for `h(T) = √(C_h log T / T)`, there are `C_a > 0` and `T₀` such that for `T ≥ T₀` and
`l, u` in the setting of p.17, with `m = (l + u)/2` and `A = (u - l)²/(2m(1 - m))`, the two divergences
`d_KL(l, u), d_KL(u, l)` are within `C_a T^(-1/3) √(log T) A` of `A`, and the four divergences
`d_KL(m, u), d_KL(u, m), d_KL(m, l), d_KL(l, m)` are within `C_a T^(-1/3) √(log T) A/4` of `A/4`.

**Formalization Note.** The page prints the additive error `C_a T^(-1/6) (log T)³`, which dwarfs the main
term (of order `(log T)/T`). This form implies the printed one, as `A ≤ 1` and
`T^(-1/3) √(log T) ≤ T^(-1/6) (log T)³` for large `T`. -/
theorem lemma_13 (Ch : ℝ) (hCh : 0 < Ch) :
    ∃ Ca : ℝ, 0 < Ca ∧ ∃ T₀ : ℝ, ∀ T ≥ T₀, ∀ l u : ℝ,
      KLSetting T l u (Real.sqrt (Ch * Real.log T / T)) →
      let m := (l + u) / 2
      let A := (u - l) ^ 2 / (2 * m * (1 - m))
      let e := Ca * T ^ (-(1 : ℝ) / 3) * Real.sqrt (Real.log T)
      |klBern l u - A| ≤ e * A ∧ |klBern u l - A| ≤ e * A ∧
      |klBern m u - A / 4| ≤ e * (A / 4) ∧ |klBern u m - A / 4| ≤ e * (A / 4) ∧
      |klBern m l - A / 4| ≤ e * (A / 4) ∧ |klBern l m - A / 4| ≤ e * (A / 4) := by sorry

end BayesBAI
