-- Prove2me | Theorems.Thm_FoundationsML_Kernels_pds_closure_properties
-- name    : FoundationsML.Kernels.pds_closure_properties
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-19T23:00:58.803268+00:00
-- url     : https://prove2.me/theorems/6510ec44-2bd9-4bf5-9393-54ee323e75b7
-- title:
--   Theorem 6.10 — PDS kernels, closure properties
-- statement:
--   **Statement (Theorem 6.10, p. 115, PDF p. 132).** PDS kernels are closed under sum,
--   product, tensor product, pointwise limit, and composition with a power series
--   $\sum_{n=0}^\infty a_n x^n$ with $a_n\ge0$ for all $n\in\mathbb N$.
--
--   This is the chapter's toolkit result, letting complex PDS kernels (Gaussian, and many
--   others) be built by combining simpler ones (e.g. polynomial kernels) rather than verifying
--   the SPSD condition from scratch each time.
--
--   **Formalization Note.** All five closure clauses are stated as one conjunction, matching
--   the book's own single theorem. Pointwise-limit closure quantifies over a sequence `Kn` of
--   PDS kernels converging pointwise (`Filter.Tendsto`) to a limit `Klim`. Power-series closure
--   adds the book's own radius-of-convergence domain restriction (`|K(x,y)| < ρ`) and an
--   explicit summability hypothesis (`hsum`) guarding the `∑'` (`tsum`) term against silently
--   evaluating to `0` for a non-summable series.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 115, Theorem 6.10 (PDF p. 132)

import Mathlib
import Definitions.Def_FoundationsML_Kernels_IsPDS

namespace FoundationsML.Kernels

/-- Theorem 6.10 (PDS kernels — closure properties; Mohri, Rostamizadeh & Talwalkar,
*Foundations of Machine Learning*, 2nd ed., MIT Press 2018, p. 115, PDF p. 132). PDS kernels
are closed under sum, product, tensor product, pointwise limit, and composition with a power
series `∑_{n=0}^∞ a_n x^n` with `a_n ≥ 0` for all `n ∈ ℕ`. -/
theorem pds_closure_properties {X : Type} (K K' : X → X → ℝ) (hK : IsPDS K) (hK' : IsPDS K') :
    IsPDS (fun x y => K x y + K' x y) ∧
    IsPDS (fun x y => K x y * K' x y) ∧
    IsPDS (fun p q : X × X => K p.1 q.1 * K' p.2 q.2) ∧
    (∀ (Kn : ℕ → X → X → ℝ) (Klim : X → X → ℝ), (∀ n, IsPDS (Kn n)) →
      (∀ x y, Filter.Tendsto (fun n => Kn n x y) Filter.atTop (nhds (Klim x y))) →
      IsPDS Klim) ∧
    (∀ (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (ρ : ℝ) (hρ : 0 < ρ) (hKb : ∀ x y, |K x y| < ρ)
       (hsum : ∀ x y, Summable (fun n => a n * (K x y) ^ n)),
       IsPDS (fun x y => ∑' n, a n * (K x y) ^ n)) := by sorry

end FoundationsML.Kernels
