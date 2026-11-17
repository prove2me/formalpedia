-- Prove2me | Theorems.Thm_AltRegret_Supplement_theorem_6
-- name    : AltRegret.Supplement.theorem_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T00:10:45.158514+00:00
-- url     : https://prove2.me/theorems/1c026a5e-eb9b-49c1-80e3-8b5625a7d2c2
-- title:
--   Theorem 6 — logarithmic dependence is necessary
-- statement:
--   Let $d\ge2$ and $T\ge d-1$. For every realized sequence $x_t\in\Delta_d$, the adaptive largest-surviving-coordinate adversary chooses costs $c_t\in[-1,1]^d$ and leaves a comparator $u\in\Delta_d$ such that
--   $$
--   \operatorname{Reg}_{\mathrm{Alt}}^T(u)\ge2\left(\sum_{m=1}^d\frac1m-1\right).
--   $$
--   Thus every online algorithm can be forced to incur the paper's exact harmonic lower bound; in particular it is $2\log d-O(1)$.
--
--   This matches the logarithmic dimension dependence of the AA-Hedge upper bound up to constants.
--
--   Differences from the source:
--   - generalization: every online algorithm interacting with an adaptive adversary → every realized simplex-valued play sequence against the explicit adaptive adversary; reason: every algorithm/adversary interaction yields such a sequence, while the proof uses only the realized actions
--   - encoding: an adaptive adversary observes x_t → surviving sets and maximizing coordinates explicitly certify that c_t depends on actions only through round t; reason: this is the adversary constructed in the proof
-- source:
--   Tao, Zheng, Optimal Alternating Regret for Online Learning and Games, arXiv:2608.24731, Theorem 6, p.9

import Mathlib
import Definitions.Def_AltRegret_altRegretAgainst
import Definitions.Def_AltRegret_Supplement_IsHarmonicAdversary

namespace AltRegret.Supplement

/-- **Theorem 6 (Logarithmic dependence is necessary).** Tao–Zheng,
*Optimal Alternating Regret for Online Learning and Games*, arXiv:2608.24731, Theorem 6,
p.9. For `d ≥ 2` and `T ≥ d-1`, the adaptive largest-surviving-mass adversary forces
alternating regret at least `2(∑_{m=1}^d 1/m - 1)`.

**Formalization Note.** Coordinates are `Fin d`. The theorem is stated for every realized
simplex-valued play sequence, which is stronger than quantifying over causal online algorithms;
`IsHarmonicAdversary` records that round `t`'s cost is selected after seeing `x_t` and uses no
future play. The comparator witness is the final surviving coordinate. -/
theorem theorem_6 {d : ℕ} (hd : 2 ≤ d) (T : ℕ) (hT : d - 1 ≤ T)
    (x : ℕ → Fin d → ℝ)
    (hx : ∀ t, 1 ≤ t → t ≤ T → x t ∈ stdSimplex ℝ (Fin d)) :
    ∃ c : ℕ → Fin d → ℝ,
      IsHarmonicAdversary x c ∧
      (∀ t, 1 ≤ t → t ≤ T → ∀ i, c t i ∈ Set.Icc (-1 : ℝ) 1) ∧
      ∃ u : Fin d → ℝ, u ∈ stdSimplex ℝ (Fin d) ∧
        2 * ((∑ m ∈ Finset.Icc 1 d, (1 : ℝ) / m) - 1) ≤
          AltRegret.altRegretAgainst x c T u := by sorry

end AltRegret.Supplement
