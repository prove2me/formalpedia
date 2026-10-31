-- Prove2me | Theorems.Thm_Erdos624_palette_size_from_mean_error
-- name    : Erdos624.palette_size_from_mean_error
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-30T14:10:52.91307+00:00
-- url     : https://prove2.me/theorems/c70cddbe-4ce2-4746-a09f-dfc4729581c4
-- title:
--   Palette size from colourwise mean error (PE) (Erdős 624)
-- statement:
--   Let $C$ be finite and $\mu:C\to\mathbb R$. Write $E\ge\sum_u|\mu(u)-2|$ and $J=\{u\in C:\mu(u)>0\}$. Then $|J|\ge |C|-E/2$. Each colour with non-positive mean contributes at least $2$ to the absolute-error sum.
--
--   Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$. These are auxiliary finite combinatorial identities from Sol's 2026-10-30 Perplexity notes. They do **not** settle Erdős Problem 624, PAIR or Step 17.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); Round 17: Sol's Perplexity Computer notes from task d32c2107-b546-4015-be2e-c9c4e46ce7cd (captured 2026-10-30 under perplexity_2026-10-30/), derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung; hand-checked and Lean-verified by Grok Bot for Ethan Cheung (Oct 30 2026). Auxiliary finite results only; do NOT settle PAIR / Step 17 / #624.

import Mathlib
open Finset

namespace Erdos624

theorem palette_size_from_mean_error {C : Type*} [Fintype C]
    (μ : C → ℝ) (E : ℝ)
    (hE : ∑ u : C, |μ u - 2| ≤ E)
    (J : Finset C) (hJ : ∀ u : C, u ∈ J ↔ 0 < μ u) :
    (Fintype.card C : ℝ) - E / 2 ≤ (#J : ℝ) := by sorry

end Erdos624
