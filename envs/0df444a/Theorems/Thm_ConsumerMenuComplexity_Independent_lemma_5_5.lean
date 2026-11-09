-- Prove2me | Theorems.Thm_ConsumerMenuComplexity_Independent_lemma_5_5
-- name    : ConsumerMenuComplexity.Independent.lemma_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:07:09.6492+00:00
-- url     : https://prove2.me/theorems/73028a69-f57c-4829-92e5-7d484cfc3c34
-- title:
--   Lemma 5.5 — the full target curve is implementable
-- statement:
--   Let $r(a)=a/4+a^2/8$ for $0\le a\le2$ and $r(a)=a-1$ for $a>2$. The single-item menu with the null option, $(1,0,1)$ and all options $((1+t)/4,0,t^2/8)$ for real $0\le t\le2$ is valid. Its defined selected mechanism is admissible, selects a maximizing option, allocates no item 2, and satisfies
--   $$u(v_1,v_2)=r(v_1)\qquad\text{for all }v_1,v_2\ge0.$$
--   This gives an explicit single-item implementation of the whole curve, including the corner at 2 and the unbounded linear tail. The second coordinate simply records that item 2 is unused.
--
--   Differences from the source:
--   - generalization: there exists a single-item menu producing r → the explicit menu and selection from the proof are valid, admissible and produce r on every nonnegative first coordinate; reason: this names the witness of the source existential and implies it
--   - encoding: one-item menu of the options ((1+t)/4, t²/8) and (1,1) → two-coordinate options with second allocation identically zero, plus the null option; reason: embedding a one-item menu with second allocation zero changes no single-item instance; §2.1 includes the null option in every menu and it is dominated
-- source:
--   Goldner, Mohan and Phung, On the Menu Complexity of Consumer Utility Maximization, November 3, 2026 preprint, STOC 2027 submission #10, SHA-256 4baa3f39e319dd0a0dd217840839edadc0a463c80f799a7858fa61ddc5de9cb4, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/10.pdf, Lemma 5.5 and its displayed witness, PDF p.21 (printed p.20); equation (13), PDF p.20

import Mathlib
import Definitions.Def_ConsumerMenuComplexity_Independent_Construction

namespace ConsumerMenuComplexity.Independent

/-- Lemma 5.5 and its explicit single-item implementation, PDF p.21 (printed p.20). -/
theorem lemma_5_5 :
    ValidMenu targetItemOneMenu ∧ Admissible targetItemOneMechanism ∧
    Selects targetItemOneMenu targetItemOneMechanism ∧
    (∀ o ∈ targetItemOneMenu, o.1 1 = 0) ∧
    (∀ v : TypeSpace, utility targetItemOneMechanism v = targetUtility (v 0)) := by sorry

end ConsumerMenuComplexity.Independent
