-- Prove2me | Theorems.Thm_Erdos287_near_target_mass_between_nested_omissions
-- name    : Erdos287.near_target_mass_between_nested_omissions
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T06:29:06.584577+00:00
-- url     : https://prove2.me/theorems/62847930-3211-4fec-b562-abb847e06fb7
-- title:
--   A fixed denominator interval admits mass within one term of a bracketed target
-- statement:
--   Let $H\subseteq G\subseteq I$ be finite sets, with rational weights $w(n)$, target $t$ and upper bound $W>0$ on each optional weight $w(n)$ for $n\in G\setminus H$. If the retained masses of $I\setminus G$ and $I\setminus H$ bracket $t$, there is a set $D$ between them whose mass lies in $[t,t+W)$. If $G$ has no consecutive pair, then no such choice of $D$ omits consecutive positions in $I$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287. Near-unit reciprocal mass with fixed endpoints and preassigned omissions.

import Mathlib

theorem Erdos287.near_target_mass_between_nested_omissions (I H G : Finset ℕ) (w : ℕ → ℚ) (t W : ℚ)
    (hHG : H ⊆ G) (hGI : G ⊆ I) (hW : 0 < W)
    (hw : ∀ n ∈ G \ H, w n ≤ W)
    (hlo : (∑ n ∈ I \ G, w n) ≤ t) (hhi : t ≤ ∑ n ∈ I \ H, w n) :
    ∃ D : Finset ℕ, I \ G ⊆ D ∧ D ⊆ I \ H ∧
      t ≤ (∑ n ∈ D, w n) ∧ (∑ n ∈ D, w n) < t + W := by sorry
