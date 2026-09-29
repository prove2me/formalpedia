-- Prove2me | Theorems.Thm_BanditAlgorithm_pinsker_inequality_total_variation
-- name    : BanditAlgorithm.pinsker_inequality_total_variation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-18T23:57:41.249808+00:00
-- url     : https://prove2.me/theorems/460cdc29-1eb4-456a-ad16-ba41228acbe0
-- statement:
--   (Pinsker, event form Eq. (14.13)) For probability measures $P, Q$ on $(\Omega,\mathcal{F})$ with $D(P,Q) = $ `klDiv P Q` finite and any measurable $A$:
--
--   $$P(A) + Q(A^c) \ge 1 - \sqrt{\frac{D(P,Q)}{2}}.$$
--
--   This is the bandit-usable form of Pinsker's inequality (Eq. (14.12))
--
--   $$\delta(P,Q) = \sup_A P(A)-Q(A) \le \sqrt{\frac{D(P,Q)}{2}};$$
--
--   the sup-form follows by instantiating the theorem at $A^c$ and rearranging with $Q(A)+Q(A^c)=1$, so no expressiveness is lost. BOUNDARY: the hypothesis $D(P,Q) \ne \infty$ is REQUIRED — at $\infty$ the junk value `(∞).toReal = 0` makes the left-hand side $1 - \sqrt{0} = 1$, but $P(A)+Q(A^c)$ can be $0$ (e.g. $P=\delta_0$, $Q=\delta_1$, $A=\{1\}$). The book's form is trivially true at $D=\infty$.
-- source:
--   L&S Ch 14.3 Note 5, Eqs. (14.12)-(14.13), p.193

import Mathlib.InformationTheory.KullbackLeibler.Basic


open MeasureTheory InformationTheory Real
open scoped ENNReal

theorem BanditAlgorithm.pinsker_inequality_total_variation {Ω : Type} {mΩ : MeasurableSpace Ω}
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {A : Set Ω} (hA : MeasurableSet A) (hD : klDiv P Q ≠ ∞) :
    1 - Real.sqrt ((klDiv P Q).toReal / 2) ≤ P.real A + Q.real Aᶜ := by
  sorry
