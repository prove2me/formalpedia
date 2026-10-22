-- Prove2me | Theorems.Thm_FibAnyon_Approx_lemma_18
-- name    : FibAnyon.Approx.lemma_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:46:31.186631+00:00
-- url     : https://prove2.me/theorems/11336e8a-d441-43c9-b58a-5844995eb7aa
-- title:
--   Lemma 18, p. 13 (corrected: n ≥ 2) — APPROX-REAL error and coefficient bounds
-- statement:
--   Let $x$ be real and $n\ge2$. If Figure 15's APPROX-REAL procedure returns integers $a,b$, then
--
--   $$|x-(a+b\tau)|\le\tau^{n-1}(1-\tau^n),\qquad |b|\le\varphi^n.$$
--
--   The first bound controls the sampler's geometric error; the second bounds the size of its cyclotomic coefficients.
--
--   **Formalization Note** The displayed error bound fails at $n=1$, so the theorem includes $n\ge2$. The paper's polynomial-time clause is not modeled here.
-- source:
--   Kliuchnikov, Bocharov, Svore, Asymptotically optimal topological quantum compiling, arXiv:1310.4150v1, p. 13, Lemma 18 (n ≥ 2 correction)

import Mathlib
import Definitions.Def_FibAnyon_Approx_Model

noncomputable section

namespace FibAnyon.Approx

/-- Lemma 18, p. 13; n ≥ 2 is necessary for the displayed error bound. -/
theorem lemma_18 (x : ℝ) (n : ℕ) (hn : 2 ≤ n) :
    let z := approxReal x n
    |x - ((z.1 : ℝ) + (z.2 : ℝ) * tau)| ≤
        tau^(n-1) * (1 - tau^n) ∧
      |(z.2 : ℝ)| ≤ gold^n := by sorry

end FibAnyon.Approx
