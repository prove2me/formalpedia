-- Prove2me | Theorems.Thm_Erdos624_growing_core_obstruction
-- name    : Erdos624.growing_core_obstruction
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-24T07:56:49.724975+00:00
-- url     : https://prove2.me/theorems/d9798d36-075a-4ee8-bb36-0f3a8d895a9b
-- title:
--   Growing-core / prescribed-star integral obstruction with $k\ge 16(t+1)^2$ (Erdős 624 auxiliary)
-- statement:
--   Let $t\ge 2$ and $k\ge 16(t+1)^2$, and let $U$ be a finite set with $|U|=2^k$. For every $B\subseteq U$ with $|B|=k-t$, there exist maps
--   $$
--   g_0,g_1:\mathcal P(U)\to U
--   $$
--   such that
--   $$
--   I_{g_0}(Y)\cup I_{g_1}(Y)=U
--   $$
--   for every $Y\in\binom{U}{k}$ with $B\subseteq Y$, where $I_g(Y)=\{g(A):A\subseteq Y\}$.
--
--   Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$. This theorem does NOT settle Problem 624 / PAIR; it only proves a prescribed-star covering obstruction (two maps can jointly cover every $k$-set through a fixed $(k-t)$-core, even for $t$ growing like $\sqrt{k}$). The corrected capacity threshold used in the proof is $A_t=[t(t+1)]^{2t+3}\cdot 2^{4t(t+1)}$.
--
--   **Formalization Note.** Pure Mathlib statement: `U` is an arbitrary `Fintype` with `Fintype.card U = 2 ^ k`; maps are `Finset U → U`. No dependence on the Erdős 624 definitions module.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); growing-core / prescribed-star obstruction (A5) derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung; Lean-verified by Grok Bot for Ethan Cheung (Oct 24 2026). Corrected $A_t=[t(t+1)]^{2t+3}\cdot 2^{4t(t+1)}$ (Sol writeup had the $2$-power in the denominator).

import Mathlib
open Finset

namespace Erdos624

/-- Growing-core / prescribed-star integral obstruction (Sol (1)+(2)).
For `t ≥ 2` and `k ≥ 16(t+1)^2`, every `(k−t)`-set `B ⊆ U` (`|U|=2^k`) admits maps
`g₀,g₁` covering `U` on every `k`-set in the star of `B`.
Does **not** settle PAIR / #624. -/
theorem growing_core_obstruction
    {U : Type*} [Fintype U] [DecidableEq U]
    {t k : ℕ} (ht : 2 ≤ t) (hk : t ≤ k) (hkk : 16 * (t + 1) ^ 2 ≤ k)
    (hU : Fintype.card U = 2 ^ k)
    (B : Finset U) (hB : #B = k - t) :
    ∃ (g0 g1 : Finset U → U),
      ∀ Y : Finset U, #Y = k → B ⊆ Y →
        (Y.powerset.image g0 ∪ Y.powerset.image g1) = (univ : Finset U) := by sorry

end Erdos624
