-- Prove2me | Theorems.Thm_Erdos462RH_short_prime_window_moment
-- name    : Erdos462RH.short_prime_window_moment
-- status  : Open
-- author  : @adamhenr
-- created : 2026-11-21T09:07:37.305654+00:00
-- url     : https://prove2.me/theorems/ca2539a4-9492-4151-a0cd-432f98a8516b
-- title:
--   A second moment and positive-density prime supply
-- statement:
--   There exists an absolute $S_0>1$ such that for real $S\ge S_0$ and every real $h$ in $[2\log S,S/4]$,
--   $$\int_S^{2S}A_h(s)^2\,ds\le 132Sh^2/(\log S)^2.$$
--   The Lebesgue measure of the $s\in[S,2S]$ for which $A_h(s)\ge h/(4\log S)$ is at least $S/2500$.
-- source:
--   Adam Henriksson, Balanced semiprimes in short intervals under the Riemann hypothesis. Lemma 3.1; D. Bazzanella, A. Languasco and A. Zaccagnini, Prime numbers in logarithmic intervals, Lemma 4, https://doi.org/10.1090/S0002-9947-09-05009-0.

import Definitions.Def_Erdos462PrimeCount

namespace Erdos462RH
theorem short_prime_window_moment :
  ∃ S₀ : ℝ, 1 < S₀ ∧ ∀ S h : ℝ, S₀ ≤ S → 2 * Real.log S ≤ h → h ≤ S/4 →
    (∫ s in S..(2*S), (primeCountWindow s h)^2) ≤
      132*S*h^2/(Real.log S)^2 ∧
    S/2500 ≤ MeasureTheory.volume.real
      {s : ℝ | s ∈ Set.Icc S (2*S) ∧ h/(4*Real.log S) ≤ primeCountWindow s h} := by sorry
end Erdos462RH
