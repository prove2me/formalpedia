-- Prove2me | Theorems.Thm_FoundationsML_RademacherVC_vc_dimension_generalization_bound
-- name    : FoundationsML.RademacherVC.vc_dimension_generalization_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-19T21:16:10.879355+00:00
-- url     : https://prove2.me/theorems/4056680d-1fbe-4f07-be75-eab9d8d35843
-- title:
--   Corollary 3.19 — VC-dimension generalization bound (goal)
-- statement:
--   **Statement (Corollary 3.19, p. 42, PDF p. 59).** Let $H$ be a family of functions taking
--   values in $\{-1,+1\}$ with VC-dimension $d$. Then, for any $\delta>0$, with probability at
--   least $1-\delta$, the following holds for all $h\in H$:
--   $$R(h) \le \hat R_S(h) + \sqrt{\frac{2d\log(em/d)}{m}} + \sqrt{\frac{\log(1/\delta)}{2m}}.$$
--
--   This is the chapter's capstone: it replaces Theorem 2.13's $\log|H|$ (which requires $H$
--   finite) with the VC-dimension $d$, extending the finite-hypothesis-set learning bound to
--   the infinite hypothesis sets used throughout machine learning, via the chain Theorem 3.3
--   (Rademacher bound) → Theorem 3.5/Corollary 3.8 (Massart's-lemma-based growth-function
--   bound) → Sauer's lemma → Corollary 3.18's $O(m^d)$ growth-function bound.
--
--   **Formalization Note.** `H : Set (X → Bool)` (possibly infinite, unlike chapter 2's
--   `Finset`); `em/d` is `Real.exp 1 * m / d`; the side condition `d ≤ m` (`hm`) is added
--   explicitly — needed for Corollary 3.18's own domain (`for all m ≥ d`), which this bound's
--   proof composes through, and dropped by neither the book nor this formalization (per
--   `BRIEF.md`'s pitfall note). `∀ h ∈ H, …` is placed inside the probability event (uniform
--   convergence), matching "the following holds for all `h ∈ H`."
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 42, Corollary 3.19 (PDF p. 59)

import Mathlib
import Definitions.Def_FoundationsML_RademacherVC_GeneralizationError
import Definitions.Def_FoundationsML_RademacherVC_EmpiricalError
import Definitions.Def_FoundationsML_RademacherVC_HasVCDim

open MeasureTheory

namespace FoundationsML.RademacherVC

/-- Corollary 3.19 (VC-dimension generalization bound; goal; Mohri, Rostamizadeh &
Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018, p. 42, PDF p. 59).
Let `H` be a family of functions taking values in `{−1,+1}` (here: `Bool`) with VC-dimension
`d`. Then, for any `δ > 0`, with probability at least `1 − δ`, the following holds for all
`h ∈ H`:
`R(h) ≤ R̂_S(h) + sqrt(2d log(em/d)/m) + sqrt(log(1/δ)/(2m))`. -/
theorem vc_dimension_generalization_bound
    {X : Type*} [MeasurableSpace X] (D : Measure X) [IsProbabilityMeasure D]
    (H : Set (X → Bool)) (d : ℕ) (hH : HasVCDim H d) (c : X → Bool)
    (m : ℕ) (hm : d ≤ m) (δ : ℝ) (hδ : 0 < δ) :
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X | ∀ h ∈ H, GeneralizationError D c h ≤
        EmpiricalError S c h +
          Real.sqrt (2 * d * Real.log (Real.exp 1 * m / d) / m) +
          Real.sqrt (Real.log (1 / δ) / (2 * m))}).toReal := by sorry

end FoundationsML.RademacherVC
