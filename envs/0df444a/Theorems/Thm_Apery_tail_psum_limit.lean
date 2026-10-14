-- Prove2me | Theorems.Thm_Apery_tail_psum_limit
-- name    : Apery.tail_psum_limit
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-12T14:45:14.802533+00:00
-- url     : https://prove2.me/theorems/1af60cb5-b63a-4fab-947e-bc4009142f7f
-- title:
--   Tail prime-sum limit: $\mathrm{psum}\,(xF+27/16)\,20\,400\,K/K^2 \le -6843153/128000000 + \delta$
-- statement:
--   For every $\delta > 0$ and all sufficiently large real $K$,
--
--   $$\frac{1}{K^2}\sum_{K/400 < p \le K/20} p\,\Bigl(\frac{K}{p}F\Bigl(\frac{K}{p}\Bigr) + \frac{27}{16}\Bigr)\log p \;\le\; -\frac{6843153}{128000000} + \delta,$$
--
--   i.e. the tail prime sum is at most $-0.0534621\ldots K^2 + o(K^2)$. This is `tail_psum_limit` of `Apery/Growth/Assembly4.lean`; it is obtained from the piecewise-linear majorant `tT`/`gT` built on the grid $t_i = 20 + i/3$ ($i \le 1140$) via `psum_piecewise_le` (Abel summation + the prime number theorem), and the numerical evaluation `tail_sum_le` of `Apery/Growth/TailIntegral.lean` (two integrations by parts per piece with telescoping). **Formalization Note** The statement is the source's; `psum` and `Ftail` are the platform definitions.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Growth/Assembly4.lean#L63-L94 (via Apery/Growth/TailIntegral.lean)

import Mathlib
import Definitions.Def_Zeta5_SourceGrowth

open Finset Filter

namespace Apery

/-- The tail prime-sum limit (`Apery/Growth/Assembly4.lean`). -/
lemma tail_psum_limit {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ K : ℝ in atTop, psum (fun x => x * Ftail x + 27 / 16) 20 400 K / K ^ 2 ≤
      -6843153 / 128000000 + δ := by
  sorry

end Apery
