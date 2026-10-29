-- Prove2me | Theorems.Thm_BramsonQueueing_Classical_reversed_rates_identify_stationarity
-- name    : BramsonQueueing.Classical.reversed_rates_identify_stationarity
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T02:18:40.871188+00:00
-- url     : https://prove2.me/theorems/1bb404c2-db26-4738-a98a-b1a021bda250
-- title:
--   Proposition 2.6 — reversed rates identify stationarity
-- statement:
--   Let $q$ be the rates of an irreducible, noninstantaneous, nonexplosive Markov process on a nonempty countable space $S$. Suppose $\widehat q(x,y)\ge0$, $\pi(x)>0$, $\sum_x\pi(x)=1$, and
--   $$\widehat q(x,y)=\frac{\pi(y)q(y,x)}{\pi(x)},\qquad \sum_yq(x,y)=\sum_y\widehat q(x,y).$$
--   Then $\pi$ is stationary for the process, and $\widehat q$ gives the rates of the reversed process in stationarity. In particular the transition kernels satisfy $\pi(x)P_t(x,y)=\pi(y)\widehat P_t(y,x)$, and the off-diagonal rates of the reversed kernel are its right-hand small-time limits. This is the chapter's identification criterion for a candidate invariant law and reversed process.
--
--   Differences from the source:
--   - reading: Eq. (2.11) prints q(y,z) with z unbound → q(y,x); reason: the proof of Proposition 2.6 and Eq. (2.23) fix the intended variable; recorded as insight I1
--   - encoding: finite nonnegative jump rates and positive probability masses → rates and masses take values in ENNReal, with finiteness enforced by Regular, equal exit rates, and normalization; reason: all off-diagonal rates and masses are finite on the stated domain; positive normalized masses guard division and finite exit rates guard toReal
--   - encoding: a nonexplosive countable-state continuous-time Markov process → its minimal transition kernel constructed by the exponential first-jump recursion; reason: the finite-rate nonexplosive process is determined by these rates; stationarity is invariance for every nonnegative time
--   - encoding: jump rates between states → zero diagonal rates explicitly; reason: diagonal events do not change the state; total exit rates sum off-diagonal jumps
--   - encoding: qhat gives the transition rates of the reversed stationary process → regularity of qhat, the reversed transition-kernel identity, and every off-diagonal right-hand small-time rate limit; reason: the Markov product formula recovers the full reversed finite-dimensional law from the kernel identity
-- source:
--   Maury Bramson, Stability of Queueing Networks, LNM 1950, Springer (2008), https://doi.org/10.1007/978-3-540-68896-9; Proposition 2.6, printed p. 26 / PDF p. 34; Eqs. (2.11), (2.18)

import Definitions.Def_BramsonQueueing_Classical_CountableProcess
open scoped NNReal ENNReal

namespace BramsonQueueing.Classical

/-- Bramson, Proposition 2.6, printed p. 26 / PDF p. 34. -/
theorem reversed_rates_identify_stationarity {S : Type*} [Countable S] [Nonempty S]
    (q qhat : S → S → ℝ≥0∞) (π : S → ℝ≥0∞)
    (hq0 : ∀ x, q x x = 0)
    (hreg : Regular q) (hirr : Communicates q)
    (hpos : ∀ x, 0 < π x) (hnorm : ∑' x, π x = 1)
    (h211 : ∀ x y, qhat x y = π y * q y x / π x)
    (h218 : ∀ x, exitRate q x = exitRate qhat x) :
    ((∑' x, π x = 1) ∧ ∀ t, 0 ≤ t → ∀ y,
      ∑' x, π x * transition q t x y = π y) ∧
    Regular qhat ∧
    (∀ t, 0 ≤ t → ∀ x y, π x * transition q t x y = π y * transition qhat t y x) ∧
    ∀ x y, x ≠ y → Filter.Tendsto
      (fun t : ℝ => (transition qhat t x y).toReal / t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (qhat x y).toReal) := by sorry

end BramsonQueueing.Classical
