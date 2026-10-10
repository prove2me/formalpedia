-- Prove2me | Theorems.Thm_DirichletUnitTheorem_sum_mult_log_eq_zero
-- name    : DirichletUnitTheorem.sum_mult_log_eq_zero
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:33:51.42382+00:00
-- url     : https://prove2.me/theorems/c56b0254-9c78-446f-8211-6dacfb541bf0
-- title:
--   $\sum_w N_w\log\lvert u\rvert_w = 0$ for every unit
-- statement:
--   Let $K$ be a number field and $u\in\mathcal O_K^\times$. Writing $\sigma_j$ for the embeddings corresponding to the infinite places and $N_j\in\{1,2\}$ for the local degrees,
--
--   $$\sum_{j} N_j\log\lvert\sigma_j(u)\rvert = 0.$$
--
--   The left side is $\log\lvert N_{K/\mathbb Q}(u)\rvert$, and units have norm $\pm1$. This is the reason the rows of the regulator matrix sum to zero.
-- source:
--   Wikipedia, "Dirichlet's unit theorem" (article supplied by the account owner as a PDF), section "The regulator" ("the sum of any row is zero (because all units have norm 1, and the log of the norm is the sum of the entries in a row)").

import Mathlib
open NumberField

namespace DirichletUnitTheorem

theorem sum_mult_log_eq_zero (K : Type*) [Field K] [NumberField K] (u : (𝓞 K)ˣ) :
    ∑ w : InfinitePlace K, (w.mult : ℝ) * Real.log (w ((u : 𝓞 K) : K)) = 0 := by sorry

end DirichletUnitTheorem
