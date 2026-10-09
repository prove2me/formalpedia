-- Prove2me | Theorems.Thm_EvenCycleTuran_EvenGirth_theta_lower_bound
-- name    : EvenCycleTuran.EvenGirth.theta_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:26:17.358479+00:00
-- url     : https://prove2.me/theorems/4a5491ce-fe11-4292-97eb-39405b7f120d
-- title:
--   p. 20 — the theta graph has only cycles of length 2l or ml and Ω(n^m) cycles of length ml
-- statement:
--   Let $k>l\ge2$ and $m\ge2$ with $2k\ne ml$. Let $\Theta_n$ be the theta-$(n,C_m,l)$ graph for $m\ge3$ and the theta-$(n,K_2,l)$ graph for $m=2$. Then
--
--   1. for every $n$, every cycle in $\Theta_n$ has length $2l$ or $ml$, so $\Theta_n$ contains no cycle of length $3,4,\dots,2l-1$ and no cycle of length $2k$;
--   2. there is a constant $c>0$ such that for all sufficiently large $n$
--   $$\mathcal N(C_{ml},\Theta_n)\ge c\,n^m .$$
--
--   This is the lower bound of Theorem 14.
--
--   **Formalization Note.** $\Theta_n$ is `thetaCycle n m l` from the Setting. The constant $c$ is chosen before $n$ and may depend on $k$, $l$, $m$.
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, p. 20, proof of Theorem 14, first paragraph (theta graph defined on p. 5; the case m = 2 is the theta-(n, K_2, l) graph of p. 6)

import Mathlib
import Definitions.Def_EvenCycleTuran_EvenGirth_Setting
open SimpleGraph Finset Filter Asymptotics

namespace EvenCycleTuran.EvenGirth

theorem theta_lower_bound (k l m : ℕ) (hl : 2 ≤ l) (hkl : l < k) (hm : 2 ≤ m)
    (hne : 2 * k ≠ m * l) :
    (∀ n r : ℕ, ∀ C : (thetaCycle n m l).Subgraph,
      IsCycleCopy (thetaCycle n m l) r C → r = 2 * l ∨ r = m * l) ∧
    (∀ n : ℕ, EvenCycleTuran.C4Count.CycleFree (Set.Icc 3 (2 * l - 1) ∪ {2 * k}) (thetaCycle n m l)) ∧
      ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
        c * (n : ℝ) ^ m ≤ ((thetaCycle n m l).copyCount (cycleGraph (m * l)) : ℝ) := by sorry

end EvenCycleTuran.EvenGirth
