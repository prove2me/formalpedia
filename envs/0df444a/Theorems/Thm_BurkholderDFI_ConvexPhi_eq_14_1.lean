-- Prove2me | Theorems.Thm_BurkholderDFI_ConvexPhi_eq_14_1
-- name    : BurkholderDFI.ConvexPhi.eq_14_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:13:54.562345+00:00
-- url     : https://prove2.me/theorems/710d4155-7fb2-49c2-867a-c2d031c35809
-- title:
--   (14.1) — Davis's martingale decomposition
-- statement:
--   For a martingale $f$, form $y_k,z_k,a_k,b_k,g_n,h_n$ by Davis's definitions in §14. Then $g$ and $h$ are martingales and
--   $$
--   f_n=g_n+h_n\qquad(n\ge1).
--   $$
--   This decomposes $f$ into a part with predictably bounded jumps and a part controlled by its large jumps.
--
--   **Formalization Note** The partial sums use the paper's $g_0=h_0=0$. To express the martingale property in Mathlib at index zero, $g$ is extended by $g_0=0$ and $h$ by $h_0=f_0$; statements about the paper's processes are for $n\ge1$.
-- source:
--   Burkholder, Distribution Function Inequalities for Martingales, Ann. Probability 1 (1973), (14.1), §14, p. 33

import Mathlib
import Definitions.Def_BurkholderDFI_ConvexPhi_Davis

namespace BurkholderDFI.ConvexPhi
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- (14.1), p. 33: Davis's decomposition into two martingales. -/
theorem eq_14_1 {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hf : Martingale f ℱ P) :
    Martingale (fun n => if n = 0 then (fun _ => (0 : ℝ)) else davisG ℱ P f n) ℱ P ∧
    Martingale (fun n => if n = 0 then f 0 else davisH ℱ P f n) ℱ P ∧
    ∀ n, 1 ≤ n → ∀ ω, f n ω = davisG ℱ P f n ω + davisH ℱ P f n ω := by sorry
end BurkholderDFI.ConvexPhi
