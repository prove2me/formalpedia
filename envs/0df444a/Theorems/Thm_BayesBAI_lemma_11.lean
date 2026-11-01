-- Prove2me | Theorems.Thm_BayesBAI_lemma_11
-- name    : BayesBAI.lemma_11
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:53:39.618778+00:00
-- url     : https://prove2.me/theorems/08881800-2691-4745-a109-4312d8683305
-- title:
--   Lemma 11 — $d_{\mathrm{KL}}$ around $l$
-- statement:
--   In the setting of Appendix C ($T^{-1/6}<\frac12$, $2h<T^{-1/6}$, $l\in[T^{-1/6},1-T^{-1/6}]$, $l<u<h+l$),
--   $$
--   \Big|d_{\mathrm{KL}}(l,u)-\frac{(u-l)^2}{2l(1-l)}\Big|\le 8\,h^3\,T^{1/3}.
--   $$
--   This is the second-order expansion of the Bernoulli divergence, with a bound uniform as $l$ approaches the boundary at rate $T^{-1/6}$.
--
--   Differences from the source:
--   - generalization: C_KL, used before it is introduced → the constant 8; reason: this is the value the proof on p.18 gives, and implies the statement with any larger C_KL (Reading 9)
--   - encoding: h(T) = o(T^(−1/6)) and a threshold T₀ with 2h(T) < T^(−1/6), T^(−1/6) < 1/2 for T ≥ T₀ → the same inequalities at one real T, as KLSetting T l u h; reason: this gives the printed statement for every such h, T₀, and shows the constants are universal
-- source:
--   Komiyama, Ariu, Kato, Qin, Rate-optimal Bayesian Simple Regret in Best Arm Identification, arXiv:2111.09885v3, Lemma 11, pp.17–18

import Mathlib
import Definitions.Def_BayesBAI_KLSetting
import Definitions.Def_RegretBandits_Stochastic_klBernoulli

namespace BayesBAI

open RegretBandits.Stochastic in
/-- Lemma 11 (bound on the KL divergence around `l`), Komiyama, Ariu, Kato, Qin, arXiv:2111.09885v3,
pp.17–18: in the setting of p.17,
`|d_KL(l, u) - (u - l)²/(2l(1 - l))| ≤ C_KL h³ T^(1/3)`.

**Formalization Note.** The constant is the proof's `8` (p.18), since `C_KL` is used before it is
introduced. -/
theorem lemma_11 {T l u h : ℝ} (hs : KLSetting T l u h) :
    |klBern l u - (u - l) ^ 2 / (2 * l * (1 - l))| ≤ 8 * h ^ 3 * T ^ ((1 : ℝ) / 3) := by sorry

end BayesBAI
