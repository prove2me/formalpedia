-- Prove2me | Theorems.Thm_FamousTheorems_tendsto_stirlingSeq_sqrt_pi
-- name    : FamousTheorems.tendsto_stirlingSeq_sqrt_pi
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T21:52:00.978982+00:00
-- url     : https://prove2.me/theorems/d770f0c3-47b2-45b8-a264-6b1aa0f04668
-- title:
--   Stirling's formula
-- statement:
--   **Stirling's approximation for the factorial.**
--
--   Writing $\mathrm{stirlingSeq}(n) = \dfrac{n!}{\sqrt{n}\,(n/e)^{n}}$,
--   $$\lim_{n\to\infty} \mathrm{stirlingSeq}(n) \;=\; \sqrt{\pi},$$
--   which is the familiar
--   $$n! \;\sim\; \sqrt{2\pi n}\left(\frac{n}{e}\right)^{n}.$$
--
--   De Moivre established the form of the asymptotic with an unidentified constant; Stirling
--   identified the constant as $\sqrt{2\pi}$. The $\log$ of the factorial is handled by comparing
--   $\sum \log k$ with $\int \log x\,dx$, and the constant is pinned down by Wallis' product for
--   $\pi$ — which is why $\pi$ appears in a statement about factorials at all.
--
--   It is the basic tool for asymptotics of binomial coefficients and hence for local limit theorems
--   in probability and entropy estimates in combinatorics.
-- source:
--   One of Freek Wiedijk's "100 theorems"; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

theorem tendsto_stirlingSeq_sqrt_pi :
    Filter.Tendsto Stirling.stirlingSeq Filter.atTop (nhds (Real.sqrt Real.pi)) := by sorry

end FamousTheorems
