-- Prove2me | Theorems.Thm_AlgMechDesign_NonOptimal_corollary_5_8
-- name    : AlgMechDesign.NonOptimal.corollary_5_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T21:46:18.552736+00:00
-- url     : https://prove2.me/theorems/20bdf415-104c-4365-afc1-a01cf3fa724e
-- title:
--   Corollary 5.8 — under truthfulness, putting ∞ outside every agent's optimal tasks does not lower the chosen make-span
-- statement:
--   Let $x(\cdot)$ be an allocation algorithm such that the Compensation-and-Bonus mechanism based on $x(\cdot)$ is truthful. Let $t$ be a positive type vector, $o$ an optimal allocation for $t$, and $M$ a real number with $M \ge t^l_j$ for all $l, j$. Let $s$ be the type vector
--   $$s^i_j = \begin{cases} t^i_j & \text{if } j \in o^i,\\ M & \text{otherwise}\end{cases}$$
--   for every agent $i$ and task $j$. Then
--   $$g\bigl(x(s),s\bigr) \;\ge\; g\bigl(x(t),t\bigr).$$
--
--   The corollary replaces the types of all agents at once; in the proof of Theorem 5.6 it is combined with the observation that $o$ is still optimal for $s$ and that every other allocation has make-span at least $M$ under $s$.
--
--   **Formalization Note** The paper's $\infty$ is the real parameter $M$, at least every entry of $t$; $\mathrm{opt}(t)$ is an arbitrary optimal allocation $o$ of $t$, fixed once for the whole statement.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games Econ. Behav. 35, 2001, p. 192, Corollary 5.8 (in the proof of Theorem 5.6)

import Mathlib
import Definitions.Def_AlgMechDesign_NonOptimal_Model

open Finset

namespace AlgMechDesign.NonOptimal

/-- Corollary 5.8 (Nisan–Ronen, p. 192). If the Compensation-and-Bonus mechanism based on `alloc`
is truthful, `t` is a positive type vector, `o` an optimal allocation for `t` and `M` at least
every entry of `t`, then for the type vector `s = sType t o M` (`sⁱ_j = tⁱ_j` if `j ∈ oⁱ`, `M`
otherwise) the allocation chosen by `alloc` at `s` has make-span at least that chosen at `t`. -/
theorem corollary_5_8 {n k : ℕ} [NeZero n] (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (htruth : Truthful alloc) (t : Fin n → Fin k → ℝ) (ht : IsType t) (o : Fin k → Fin n)
    (ho : IsOptimalFor t o) (M : ℝ) (hM : ∀ i j, t i j ≤ M) :
    makespan t (alloc t) ≤ makespan (sType t o M) (alloc (sType t o M)) := by sorry

end AlgMechDesign.NonOptimal
