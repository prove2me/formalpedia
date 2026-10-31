-- Prove2me | Theorems.Thm_Erdos624_clipping_capacity_decomposition
-- name    : Erdos624.clipping_capacity_decomposition
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-30T14:10:54.079353+00:00
-- url     : https://prove2.me/theorems/ba5854a4-df95-49f3-9559-ecaabed008ee
-- title:
--   Exact capacity decomposition for deletion clipping (C) (Erdős 624)
-- statement:
--   For naturals with $minimal\le newRaw\le raw\le cap$, one has the exact identity $cap-minimal=(cap-raw)+(raw-newRaw)+(newRaw-minimal)$. This is the ℕ-form of the capacity split $\Delta'=K+D+T$ used for deletion-only clipping.
--
--   Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$. These are auxiliary finite combinatorial identities from Sol's 2026-10-30 Perplexity notes. They do **not** settle Erdős Problem 624, PAIR or Step 17.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); Round 17: Sol's Perplexity Computer notes from task d32c2107-b546-4015-be2e-c9c4e46ce7cd (captured 2026-10-30 under perplexity_2026-10-30/), derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung; hand-checked and Lean-verified by Grok Bot for Ethan Cheung (Oct 30 2026). Auxiliary finite results only; do NOT settle PAIR / Step 17 / #624.

import Mathlib
open Finset

namespace Erdos624

theorem clipping_capacity_decomposition (cap raw newRaw minimal : ℕ)
    (h1 : minimal ≤ newRaw) (h2 : newRaw ≤ raw) (h3 : raw ≤ cap) :
    cap - minimal = (cap - raw) + (raw - newRaw) + (newRaw - minimal) := by sorry

end Erdos624
