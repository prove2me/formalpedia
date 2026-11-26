-- Prove2me | Theorems.Thm_CondMat0408017_log_transmission_localization_length
-- name    : CondMat0408017.log_transmission_localization_length
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-26T13:24:36.543806+00:00
-- url     : https://prove2.me/theorems/9ed87240-9749-5d1d-a974-00690642b59b
-- title:
--   Eqs. (143)-(145): $\langle\ln T\rangle$ separates ohmic loss, and the localization length is the slope of a straight-line fit
-- statement:
--   Let $k_2>0$ and $\ell_\varepsilon=1/(2k_2)$. For each length $L$ of the rough segment, let $t_L$ be a random complex number with $1+t_L\ne0$ almost surely and $\ln|1+t_L|^2$ integrable. Let the SPP transmission coefficient be $T(L)=|1+t_L|^2e^{-L/\ell_\varepsilon}$ (eq. 144). Then:
--
--   1. (eq. 145) $\langle\ln T(L)\rangle=\langle\ln|1+t_L|^2\rangle-L/\ell_\varepsilon$ for every $L$.
--   2. If, with leakage neglected, $\langle\ln|1+t_L|^2\rangle=\text{const}-L/\ell$ at lengths $L_1,\dots,L_m$ that are not all equal, then the least-squares straight line through the points $(L_i,\langle\ln|1+t_{L_i}|^2\rangle)$ has slope $-1/\ell$. So the localization length $\ell$ is obtained from a straight-line fit.
--
--   **Formalization Note** The form of $T(L)$ and $t(\omega)$ is quoted from Ref. [MP2] and is a hypothesis. The paper's "$\langle\ln|1+t|^2\rangle=\text{const}-L/\ell$" is the modelling assumption that leakage is negligible, also a hypothesis. The statement records what follows from it.
-- source:
--   I. Simonsen, A random walk through surface scattering phenomena: Theory and phenomenology, arXiv:cond-mat/0408017v1 (2004), claim c029; Sec. IV.B.3, eqs. (Eq:Loc:def-transmission-rewritten), (Eq:Phen:loc-length) [(143)-(145)] and the text after them, PDF pp. 50-51

import Mathlib
import Definitions.Def_CondMat0408017_Basic

open MeasureTheory Filter Topology Complex

namespace CondMat0408017

theorem log_transmission_localization_length {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (k2 : ℝ) (hk2 : 0 < k2) (t : ℝ → Ω → ℂ) (TL : ℝ → Ω → ℝ)
    (h144 : ∀ L w, TL L w = ‖1 + t L w‖ ^ 2 * Real.exp (-(L / ohmicMeanFreePath k2)))
    (hne : ∀ L, ∀ᵐ w ∂P, 1 + t L w ≠ 0)
    (hint : ∀ L, Integrable (fun w => Real.log (‖1 + t L w‖ ^ 2)) P) :
    (∀ L, ∫ w, Real.log (TL L w) ∂P =
      (∫ w, Real.log (‖1 + t L w‖ ^ 2) ∂P) - L / ohmicMeanFreePath k2) ∧
    ∀ (ℓ C : ℝ) (m : ℕ) (Ls : Fin m → ℝ), ℓ ≠ 0 → (∃ i j, Ls i ≠ Ls j) →
      (∀ i, ∫ w, Real.log (‖1 + t (Ls i) w‖ ^ 2) ∂P = C - Ls i / ℓ) →
      olsSlope Ls (fun i => ∫ w, Real.log (‖1 + t (Ls i) w‖ ^ 2) ∂P) = -(1 / ℓ) := by sorry

end CondMat0408017
