-- Prove2me | Theorems.Thm_Arxivcond_mat_0004049_rayleigh_law_localized
-- name    : Arxivcond_mat_0004049.rayleigh_law_localized
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T20:09:06.663155+00:00
-- url     : https://prove2.me/theorems/06f846cd-b498-59a2-b645-835b91d450d6
-- title:
--   Eq. (1): Rayleigh's law for the reflected intensity (localized regime)
-- statement:
--   Let $\gamma>0$. In the localized regime the reflected intensity (unit incident intensity) follows Rayleigh's law, eq. (1).
--
--   (i) For $n\ne m$ and every $N\ge1$, $I=|A_0|^2$ has the density $P(I)=\Theta(I)\,Ne^{-NI}$.
--
--   (ii) For $n=m$, $I=|C_0|^2$ has $P(I)=\frac12Ne^{-NI/2}$ in the large-$N$ limit: $NI$ converges in law to the density $\Theta(x)\frac12e^{-x/2}$.
--
--   **Formalization Note** Only the localized-regime half of eq. (1) is stated. The diffusive-regime half rests on diffusion theory, which the paper does not state. For $n=m$, $|C_0|^2\le1$ at finite $N$, so the formula holds only in the large-$N$ limit, which is stated on the scale $NI$.
-- source:
--   Schomerus, van Bemmel and Beenakker, Coherent backscattering effect on wave dynamics in a random medium, arXiv:cond-mat/0004049v1 (2000), claim c022; eq. (1), PDF p. 1

import Mathlib
import Definitions.Def_Arxivcond_mat_0004049_Basic

open MeasureTheory Filter Topology

namespace Arxivcond_mat_0004049

theorem rayleigh_law_localized (γ : ℝ) (hγ : 0 < γ) :
    (∀ N : ℕ, 1 ≤ N → (localizedModel N γ).map intensityNe =
      (volume : Measure ℝ).withDensity
        (fun I => ENNReal.ofReal (if 0 < I then (N : ℝ) * Real.exp (-(N : ℝ) * I) else 0))) ∧
    LawTendsto γ (fun N (ω : Sample N) => (N : ℝ) * intensityEq ω)
      ((volume : Measure ℝ).withDensity
        (fun x => ENNReal.ofReal (if 0 < x then Real.exp (-x / 2) / 2 else 0))) := by sorry

end Arxivcond_mat_0004049
