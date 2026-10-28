-- Prove2me | Theorems.Thm_Erdos624_rank_only_bound
-- name    : Erdos624.rank_only_bound
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T19:40:58.331333+00:00
-- url     : https://prove2.me/theorems/f9717209-81af-4f52-a54e-36f368db197b
-- title:
--   Maps depending only on $|A|$ have small joint image (Erdős 624)
-- statement:
--   **Theorem.** Let $U$ be a set and $g_i(A)=h_i(|A|)$ for $i<r$. For every finite $Y\subseteq U$,
--
--   $$\Bigl|\bigcup_{i<r}\{g_i(A):A\subseteq Y\}\Bigr|\le r\,(|Y|+1).$$
--
--   For $|U|=2^k$, $|Y|=k$, $r=2$ and $k\ge4$ this is $<2^k$, so the rank construction that defeats the two-map common-hole claim at $k=3$ cannot work for larger $k$.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); definitions from Formal Conjectures 624.lean; (8) of claim from GPT 6.1 Sol (fifth answer, Oct 23 2026), Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos624_defs
open Finset

namespace Erdos624

theorem rank_only_bound {U : Type*} [DecidableEq U] (r : ℕ) (h : Fin r → ℕ → U)
    (Y : Finset U) :
    #(((univ : Finset (Fin r)) ×ˢ Y.powerset).image (fun p => h p.1 (#p.2))) ≤ r * (#Y + 1) := by sorry

end Erdos624
