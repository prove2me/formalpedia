-- Prove2me | Theorems.Thm_ChoresEFX_theorem_3_4
-- name    : ChoresEFX.theorem_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:08:33.649295+00:00
-- url     : https://prove2.me/theorems/16195af3-42bb-4c18-8823-fd2b488e45b9
-- title:
--   Theorem 3.4 — SSR returns a complete allocation with (6), (7), (8) and MPB ownership edges (running-time clause carried by Theorem 1.1)
-- statement:
--   Let $\beta>0$, $p>0$, let $w\ge0$ with $\sum_iw_{ig}=1$, let $H=\{g:p_g>\beta\}$, and take any sort orders. An admissible matching exists, and for every admissible matching the bundles $Y$ form a complete allocation with
--
--   $$q(Y_i)\ge E_i-\beta,\qquad q(Y_i)-\max_{g\in Y_i}q_g\le E_i,\qquad |Y_i\cap H|\le\Big\lceil\sum_{g\in H}w_{ig}\Big\rceil.$$
--
--   Every chore goes to an agent with a positive share of it. If $(p,\gamma,w)$ is a capped-price structure for $C$ with parameter $t$, then $C_{\sigma(g)}(g)\le(1+t)\gamma_{\sigma(g)}p_g$ for every chore $g$, where $\sigma(g)$ is its owner.
--
--   This controls the loss from rounding and the number of high-price chores per agent.
--
--   **Formalization Note** A maximum over the empty bundle is read as $0$.
--
--   Differences from the source:
--   - reading: Algorithm 3 runs in O(nm log m + (m+n)^{5/2}) time → the operation count is not stated here; the goal theorem_1_1 carries the running time on its machine; reason: the procedure takes real-valued data; the count is an arithmetic one (paper.md decision 7)
--   - reading: returns a complete allocation → an admissible matching exists, and the bounds hold for every sort order and every admissible matching; reason: the strongest reading of an algorithm with free choices (paper.md decision 8)
--   - generalization: input is a certificate (p, γ, w), and β < 1 → any positive p, any β > 0 and any w ≥ 0 with unit column sums; the MPB clause assumes the certificate; reason: the three bounds use nothing more, and the statement specializes to the certificate
--   - encoding: dummy chores and a perfect matching of the chore-slot support graph → an injective map on real chores along positive shares that covers every full slot; reason: equivalent over all dummy placements (paper.md decision 9)
--   - generalization: n ≥ 2 agents (standing, §2, p.5) → any finite agent type; reason: the argument does not use n ≥ 2, and the statement specializes to n ≥ 2
--   - reading: the MPB ratios γ_i of Definition 2.3 (γ_i = min_g Ĉ_i(g)/p_g, p.5) → γ is data of the structure, constrained by (3) and (4); reason: Definition 2.3 lists (3) as a condition, so γ can be read as data; this is the more general reading of the hypothesis, and the MPB ratio satisfies it
-- source:
--   Qin, Fang, Li, Liu, Chen, Polynomial-Time Approximate EFX for Chores via Flow and Matching, STOC 2027 submission (manuscript sha256 b26d14cf…), Theorem 3.4, p.10

import Mathlib
import Definitions.Def_ChoresEFX_IsAdmissibleMatching

namespace ChoresEFX

open Finset

/-- **Theorem 3.4** (running-time clause carried by Theorem 1.1), p.10.

Qin, Fang, Li, Liu, Chen, *Polynomial-Time Approximate EFX for Chores via Flow and Matching*, STOC 2027
submission (manuscript sha256 b26d14cf…).

Let `H = {g : p_g > β}`. Algorithm 3 returns a complete allocation with (6) `q(Y_i) ≥ E_i − β`,
(7) `q(Y_i) − max_{g ∈ Y_i} q_g ≤ E_i`, (8) `|Y_i ∩ H| ≤ ⌈∑_{g ∈ H} w_ig⌉`, and all ownership edges for real
chores retain the approximate MPB guarantee.

**Formalization Note.** An admissible matching exists, and the conclusion holds for every sort order and
every admissible matching. The allocation is complete since `π` is a function on the chores. The clause
`O(nm log m + (m+n)^{5/2})` counts operations on real-valued data and is carried by the goal's machine
(paper.md decision 7). -/
theorem theorem_3_4 {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] (β : ℝ) (hβ : 0 < β)
    (p : κ → ℝ) (hp : ∀ g, 0 < p g) (w : ι → κ → ℝ) (hw : ∀ i g, 0 ≤ w i g)
    (hw1 : ∀ g, ∑ i, w i g = 1) (o : ι → κ → ℕ) (ho : IsSortedOrder β p o) :
    (∃ π : κ → Σ i, Fin (numSlots w i), IsAdmissibleMatching w o π) ∧
    ∀ π : κ → Σ i, Fin (numSlots w i), IsAdmissibleMatching w o π →
      (∀ i,
        cappedIncome β p w i - β ≤ priceOf (capped β p) (ssrBundle π i) ∧
        priceOf (capped β p) (ssrBundle π i) - maxOn (capped β p) (ssrBundle π i) ≤
          cappedIncome β p w i ∧
        (((ssrBundle π i).filter fun g => β < p g).card : ℝ) ≤
          (⌈∑ g ∈ univ.filter (fun g => β < p g), w i g⌉₊ : ℝ)) ∧
      (∀ g, 0 < w (π g).1 g) ∧
      (∀ (C : ι → κ → ℝ) (t : ℝ) (γ : ι → ℝ), IsCappedPriceStructure C t β p γ w →
        ∀ g, C (π g).1 g ≤ (1 + t) * γ (π g).1 * p g) := by sorry

end ChoresEFX
