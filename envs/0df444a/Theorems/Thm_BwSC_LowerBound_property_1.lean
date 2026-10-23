-- Prove2me | Theorems.Thm_BwSC_LowerBound_property_1
-- name    : BwSC.LowerBound.property_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:35:05.517998+00:00
-- url     : https://prove2.me/theorems/dd377889-2829-4712-8d6f-9b488b942298
-- title:
--   Property 1, p. 72 — each risky event is decided by the stopped record: P′_{j,k}(E^(1)_{j,k}) = P^(1)_{j,k}(E^(1)_{j,k}), Q′_{j,k}(E^(1)_{j,k}) = ℚ(E^(1)_{j,k}), same for P″, Q″
-- statement:
--   For every policy $\pi$, every $j\in[q(S,K)+2]$ and $k\in[K]$, let $\sigma$ be the stopped-record map of the window of $j$ and arm $k$ (it keeps the rounds before the window and the rounds of the window before the first pull of $k$ there, and replaces the first pull of $k$ in the window and everything after it by $(k,0)$). Then the risky event is decided by the record:
--   $$\sigma^{-1}\big(E^{(1)}_{j,k}\big)=E^{(1)}_{j,k},$$
--   and consequently
--   $$\mathbb P'_{j,k}\big(E^{(1)}_{j,k}\big)=\mathbb P^{(1)}_{j,k}\big(E^{(1)}_{j,k}\big),\qquad \mathbb Q'_{j,k}\big(E^{(1)}_{j,k}\big)=\mathbb Q\big(E^{(1)}_{j,k}\big),$$
--   and the same three statements hold for the second class with $E^{(2)}_{j,k}$, $\mathbb P''_{j,k}$, $\mathbb Q''_{j,k}$ and the second-class windows.
--
--   This lets (46)–(47) represent $\overline{p^{(c)}}$ and $\overline{q^{(c)}}$ through the artificial measures, whose divergences are small.
--
--   **Formalization Note** The artificial measures are the repaired (stopped) form of (45) described in `BwSC.LowerBound.Proof`. For $E^{(1)}_{q+2,k}$, which involves the stopping time $\tau$, the identity holds because the record shows every action up to the first pull of $k$ in the window and no switch afterwards.
-- source:
--   Simchi-Levi & Xu, Phase Transitions in Bandits with Switching Constraints, arXiv:1905.10825v4, p. 72, property 1 of the artificial measures (used in J.5, p. 74)

import Mathlib
import Definitions.Def_BwSC_LowerBound_Proof

open MeasureTheory ProbabilityTheory InformationTheory BanditAlgorithm
open scoped ENNReal

namespace BwSC.LowerBound

/-- Property 1, p. 72 (for the stopped records): every risky event is decided by the stopped
record of its window, `stopCensor⁻¹(E) = E`, hence `P'_{j,k}(E^{(1)}_{j,k}) = P^{(1)}_{j,k}(E^{(1)}_{j,k})`
and `Q'_{j,k}(E^{(1)}_{j,k}) = ℚ(E^{(1)}_{j,k})`, and likewise for the second class with
`P''_{j,k}`, `Q''_{j,k}`. -/
theorem property_1 {K S T : ℕ} (π : BanditPolicy K) (j : ℕ)
    (hj : j ∈ Finset.Icc 1 (qIdx S K + 2)) (k : Fin K) :
    stopCensor (lo1 S K T j) (hi1 S K T j) k ⁻¹' E1 S K T j k = E1 S K T j k ∧
    artP1 π S T j k (E1 S K T j k) =
      (banditMeasure (gaussianBandit (envAlt1 S K T j k)) π T) (E1 S K T j k) ∧
    artQ1 π S T j k (E1 S K T j k) =
      (banditMeasure (gaussianBandit (0 : Fin K → ℝ)) π T) (E1 S K T j k) ∧
    stopCensor (lo2 S K T j) (hi2 S K T j) k ⁻¹' E2 S K T j k = E2 S K T j k ∧
    artP2 π S T j k (E2 S K T j k) =
      (banditMeasure (gaussianBandit (envAlt2 S K T j k)) π T) (E2 S K T j k) ∧
    artQ2 π S T j k (E2 S K T j k) =
      (banditMeasure (gaussianBandit (0 : Fin K → ℝ)) π T) (E2 S K T j k) := by sorry

end BwSC.LowerBound
