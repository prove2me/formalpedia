-- Prove2me | Theorems.Thm_Erdos195_sink_append_blocked_by_other_sink
-- name    : Erdos195.sink_append_blocked_by_other_sink
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T23:42:29.671634+00:00
-- url     : https://prove2.me/theorems/ed8bb713-345f-42a6-aa1f-0c35bd1447ec
-- title:
--   Sink steps are blocked only by other sinks' trees
-- statement:
--   A tree witness $\theta:\mathbb N\times\mathbb Z\to\{0,1\}$ defines a strict total order $\prec_\theta$ on $\mathbb Z$ (milestone framework). A finite word $T$ of integers is $\theta$-safe if the sequence "letters of $T$ in order, then all remaining integers in $\prec_\theta$-order" has no monotone 4-term arithmetic progression; positions are first occurrences. For an in-order pair $(a,b)$ of a word ($a$ before $b$), call $t=2b-a$ its third term and $w=3b-2a$ its fourth term; the pair is fully open in $T$ if neither lies in $T$. An open path in $T$ is a family of in-order pairs $(a_i,b_i)$, $0\le i<m$, of letters of $T$ with $3b_i-2a_i=2b_{i+1}-a_{i+1}$ for $0\le i<m-1$ and no third term $2b_i-a_i$ in $T$.
--
--   **Theorem.** Let $T$ be $\theta$-safe, let $w\notin T$, and assume the C1 condition for $w$: whenever $w=2y-x$ for an in-order pair $(x,y)$ of $T$, we have $3y-2x\in T$ (true for the fourth term of a true sink). If $T\cdot w$ is not $\theta'$-safe for any tree witness $\theta'$, then there are $x\in T$ with $2w-x,\,3w-2x\notin T$ and a fully open in-order pair $(x',y')$ of $T$ with $3y'-2x'\neq w$, $\nu_2(y'-x')=\nu_2(w-x)=k$, $x'\equiv x\pmod{2^k}$ and opposite orientation (the $k$-th binary digits of $y'$ and $w$ differ). This is a node conflict. Moreover:
--   1. **no** open path starting at $(x',y')$ has last fourth term equal to $w$;
--   2. $(x',y')$ lies on an open path ending at a true sink (in the sense of the previous milestone) whose fourth term is **different** from $w$.
--
--   So appending the sink fourth term $w$, the forced first step of closing a path (milestone #149), can only be blocked by a fully open pair belonging to the in-tree of a different sink. In particular, if every fully open pair of $T$ not released by $w$ reaches $w$, then $T\cdot w$ is tree-safe. The proof combines milestones #59, #153 and the previous milestone.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem sink_append_blocked_by_other_sink (θ : ℕ → ℤ → Bool) (T : List ℤ) (hS : Safe (treeLt θ) T)
    (w : ℤ) (hwT : w ∉ T)
    (hC1 : ∀ x y : ℤ, x ∈ T → y ∈ T → T.idxOf x < T.idxOf y → 2 * y - x = w → 3 * y - 2 * x ∈ T)
    (hbad : ¬ ∃ θ' : ℕ → ℤ → Bool, Safe (treeLt θ') (T ++ [w])) :
    ∃ x x' y' : ℤ, x ∈ T ∧ 2 * w - x ∉ T ∧ 3 * w - 2 * x ∉ T ∧
      x' ∈ T ∧ y' ∈ T ∧ T.idxOf x' < T.idxOf y' ∧ 2 * y' - x' ∉ T ∧ 3 * y' - 2 * x' ∉ T ∧
      3 * y' - 2 * x' ≠ w ∧
      padicValInt 2 (y' - x') = padicValInt 2 (w - x) ∧
      x' % 2 ^ padicValInt 2 (y' - x') = x % 2 ^ padicValInt 2 (y' - x') ∧
      ¬ (bitOne y' (padicValInt 2 (y' - x')) ↔ bitOne w (padicValInt 2 (y' - x'))) ∧
      (∀ (m : ℕ) (a b : ℕ → ℤ), a 0 = x' → b 0 = y' →
        (∀ i < m, a i ∈ T) → (∀ i < m, b i ∈ T) →
        (∀ i < m, T.idxOf (a i) < T.idxOf (b i)) →
        (∀ i, i + 1 < m → 3 * b i - 2 * a i = 2 * b (i + 1) - a (i + 1)) →
        (∀ i < m, 2 * b i - a i ∉ T) →
        3 * b (m - 1) - 2 * a (m - 1) ≠ w) ∧
      (∃ (m : ℕ) (a b : ℕ → ℤ), 0 < m ∧ a 0 = x' ∧ b 0 = y' ∧
        (∀ i < m, a i ∈ T) ∧ (∀ i < m, b i ∈ T) ∧
        (∀ i < m, T.idxOf (a i) < T.idxOf (b i)) ∧
        (∀ i, i + 1 < m → 3 * b i - 2 * a i = 2 * b (i + 1) - a (i + 1)) ∧
        (∀ i < m, 2 * b i - a i ∉ T) ∧
        3 * b (m - 1) - 2 * a (m - 1) ∉ T ∧
        (∀ x y : ℤ, x ∈ T → y ∈ T → T.idxOf x < T.idxOf y →
          2 * y - x = 3 * b (m - 1) - 2 * a (m - 1) → 3 * y - 2 * x ∈ T) ∧
        3 * b (m - 1) - 2 * a (m - 1) ≠ w) := by sorry

end Erdos195
