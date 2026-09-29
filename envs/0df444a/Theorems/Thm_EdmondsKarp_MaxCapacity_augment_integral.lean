-- Prove2me | Theorems.Thm_EdmondsKarp_MaxCapacity_augment_integral
-- name    : EdmondsKarp.MaxCapacity.augment_integral
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:19:23.974107+00:00
-- url     : https://prove2.me/theorems/07ff58a4-9a33-4c57-a8d0-75337a2c2a3b
-- title:
--   With integer capacities, $\varepsilon$ is a positive integer and augmentation preserves integrality
-- statement:
--   Let $N$ be a network in which every capacity $c(u,v)$ is an integer, let $f$ be an integer-valued flow in $N$, and let $P$ be an augmenting path relative to $f$. Then the augmentation $\varepsilon$ of $P$ is a positive integer,
--   $$\varepsilon \in \{1, 2, 3, \dots\},$$
--   and the augmented flow $f'$ is again integer-valued on every arc of $N$.
--
--   By induction, a run of the labeling method started from an integer-valued flow consists of integer-valued flows only. This is what turns the geometric decrease of the gap $f^*(t,s) - f^k(t,s)$ into a bound on the number of augmentations in Theorem 2.
--
--   **Formalization Note** Integer-valued means $f(u,v)\in\mathbb Z$ on the arcs of $A$ and on the return arc; values of `f` off the arcs of $N$ are not constrained.
-- source:
--   Edmonds, Karp, Theoretical Improvements in Algorithmic Efficiency for Network Flow Problems, J. ACM 19(2), 1972, p. 250, §1.1 (unnumbered: "Assuming that all the capacities c(u, v) are integers, then clearly for any augmenting path P relative to any integer-valued flow f, ε is a positive integer. …"); used on p. 254 ("since all the capacities are integers, each flow is integral")

import Mathlib
import Definitions.Def_EdmondsKarp_MaxCapacity_Network
import Definitions.Def_EdmondsKarp_MaxCapacity_Augmentation

namespace EdmondsKarp.MaxCapacity

/-- §1.1, p. 250: if all capacities are integers, then for any augmenting path `P` relative to any
integer-valued flow `f`, `ε` is a positive integer, and the augmented flow is again integer-valued. -/
theorem augment_integral {V : Type} [Fintype V] [DecidableEq V] (N : Network V)
    (hcap : IntegralCaps N) (f : V → V → ℝ) (P : List V) (hf : IsFlow N f)
    (hfint : IsIntegralOn N f) (hP : IsAugPath N f P) :
    (∃ z : ℤ, 0 < z ∧ pathEps N f P = z) ∧ IsIntegralOn N (augment N f P) := by sorry

end EdmondsKarp.MaxCapacity
