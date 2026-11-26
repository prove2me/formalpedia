-- Prove2me | Theorems.Thm_CondMat0408017_enhanced_backscattering_factor_two
-- name    : CondMat0408017.enhanced_backscattering_factor_two
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-26T13:23:21.018147+00:00
-- url     : https://prove2.me/theorems/b39e435f-c63b-5e77-b50a-05adadccb829
-- title:
--   Sec. IV.A.1: without single scattering the enhanced backscattering peak is twice its background
-- statement:
--   Model the amplitude scattered in a given direction as $S+\sum_j(A_j+B_j)$. Here $S$ is the single-scattering amplitude, and $A_j,B_j$ are the amplitudes of a multiply scattered path and of its reciprocal partner (same scattering centres, opposite order), for $j$ in a finite set. All are square-integrable random variables. Consider two directions: the backscattering direction (subscript b) and a direction away from it (subscript a). Assume:
--
--   - in the backscattering direction the two reciprocal paths coincide, $B_{b,j}=A_{b,j}$;
--   - away from it they are incoherent, $\langle A_{a,j}\bar B_{a,j}\rangle=0$, and their intensities equal those at the peak, $\langle|A_{a,j}|^2\rangle=\langle|B_{a,j}|^2\rangle=\langle|A_{b,j}|^2\rangle$;
--   - in both directions the pair sums of different pairs are mutually incoherent, $\langle(A_i+B_i)\overline{(A_j+B_j)}\rangle=0$ for $i\ne j$, and each pair sum is incoherent with single scattering, $\langle S\,\overline{(A_j+B_j)}\rangle=0$; the single-scattering intensity is the same in both, $\langle|S_a|^2\rangle=\langle|S_b|^2\rangle$;
--   - multiple scattering is present, $\sum_j\langle|A_{b,j}|^2\rangle>0$.
--
--   Let $I_b$ and $I_a$ be the mean intensities in the two directions. If there is no single scattering ($\langle|S_b|^2\rangle=0$), then $I_b=2I_a$: the enhanced backscattering peak is twice its background. If single scattering contributes ($\langle|S_b|^2\rangle>0$), then $I_b<2I_a$, so the peak is not twice its background.
--
--   **Formalization Note** The paper's argument is verbal. The model makes its assumptions explicit: equal amplitude and phase of reciprocal partners in the backscattering direction, incoherence and additive intensities away from it, and incoherence between different pairs and with single scattering. "Background" is the intensity away from the peak with the same single- and multiple-path intensities. The mechanism itself is attributed to McGurn et al. (1985) and West and O'Donnell (1995).
-- source:
--   I. Simonsen, A random walk through surface scattering phenomena: Theory and phenomenology, arXiv:cond-mat/0408017v1 (2004), claim c047; Sec. IV.A.1, text discussing Fig. (Fig:Phen:BS-origin), PDF p. 41

import Mathlib
import Definitions.Def_CondMat0408017_Basic

open MeasureTheory Filter Topology Complex

namespace CondMat0408017

theorem enhanced_backscattering_factor_two {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {J : Type*} [Fintype J] (Sb Sa : Ω → ℂ) (Ab Bb Aa Ba : J → Ω → ℂ)
    (hS : MemLp Sb 2 P ∧ MemLp Sa 2 P)
    (hA : ∀ j, MemLp (Ab j) 2 P ∧ MemLp (Bb j) 2 P ∧ MemLp (Aa j) 2 P ∧ MemLp (Ba j) 2 P)
    (hrecip : ∀ j, Bb j = Ab j)
    (hincoh : ∀ j, ∫ w, Aa j w * starRingEnd ℂ (Ba j w) ∂P = 0)
    (hpairsb : ∀ i j, i ≠ j →
      ∫ w, (Ab i w + Bb i w) * starRingEnd ℂ (Ab j w + Bb j w) ∂P = 0)
    (hpairsa : ∀ i j, i ≠ j →
      ∫ w, (Aa i w + Ba i w) * starRingEnd ℂ (Aa j w + Ba j w) ∂P = 0)
    (hsingb : ∀ j, ∫ w, Sb w * starRingEnd ℂ (Ab j w + Bb j w) ∂P = 0)
    (hsinga : ∀ j, ∫ w, Sa w * starRingEnd ℂ (Aa j w + Ba j w) ∂P = 0)
    (hsame : ∀ j, ∫ w, ‖Aa j w‖ ^ 2 ∂P = ∫ w, ‖Ab j w‖ ^ 2 ∂P ∧
      ∫ w, ‖Ba j w‖ ^ 2 ∂P = ∫ w, ‖Ab j w‖ ^ 2 ∂P)
    (hsingle : ∫ w, ‖Sa w‖ ^ 2 ∂P = ∫ w, ‖Sb w‖ ^ 2 ∂P)
    (hmult : 0 < ∑ j, ∫ w, ‖Ab j w‖ ^ 2 ∂P) :
    (∫ w, ‖Sb w‖ ^ 2 ∂P = 0 →
      ∫ w, ‖Sb w + ∑ j, (Ab j w + Bb j w)‖ ^ 2 ∂P =
        2 * ∫ w, ‖Sa w + ∑ j, (Aa j w + Ba j w)‖ ^ 2 ∂P) ∧
    (0 < ∫ w, ‖Sb w‖ ^ 2 ∂P →
      ∫ w, ‖Sb w + ∑ j, (Ab j w + Bb j w)‖ ^ 2 ∂P <
        2 * ∫ w, ‖Sa w + ∑ j, (Aa j w + Ba j w)‖ ^ 2 ∂P) := by sorry

end CondMat0408017
