-- Prove2me | Theorems.Thm_AlgMechDesign_NonOptimal_claim_5_7
-- name    : AlgMechDesign.NonOptimal.claim_5_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T21:42:16.785987+00:00
-- url     : https://prove2.me/theorems/5756cf8a-85be-4c8d-abea-e53df3e84edd
-- title:
--   Claim 5.7 — under truthfulness, putting ∞ outside an agent's optimal tasks does not lower the chosen make-span
-- statement:
--   Let $x(\cdot)$ be an allocation algorithm for task scheduling such that the Compensation-and-Bonus mechanism based on $x(\cdot)$ is truthful. Let $t$ be a positive type vector, $o$ an optimal allocation for $t$ (written $\mathrm{opt}(t)$ in the paper), and $M$ a real number with $M \ge t^l_j$ for all agents $l$ and tasks $j$. Fix an agent $i$ and let
--   $$t'^i_j = \begin{cases} t^i_j & \text{if } j \in o^i,\\ M & \text{otherwise},\end{cases}$$
--   and let $t' = (t'^i, t^{-i})$ be the type vector in which only agent $i$'s type is replaced. Then
--   $$g\bigl(x(t'),t'\bigr) \;\ge\; g\bigl(x(t),t\bigr).$$
--
--   This is the claim inside the proof of Theorem 5.6. Its content is an incentive argument: if the inequality failed, an agent of true type $t^i$ would profit from declaring $t'^i$ (a lie the mechanism cannot detect), since its bonus is the negative make-span computed from its own actual times and the others' declarations. Iterating it over the agents gives Corollary 5.8.
--
--   **Formalization Note** The paper states the claim for agent 1; here it is stated for an arbitrary agent $i$, which is what the iteration in Corollary 5.8 uses. The paper's "$\infty$ (an arbitrary high value)" is the real parameter $M$, required to be at least every entry of $t$ so that $t'^i \ge t^i$ entrywise. Truthfulness is in the sense of Definition 19 for mechanisms with verification (declaration plus execution plan).
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games Econ. Behav. 35, 2001, p. 192, Claim 5.7 (in the proof of Theorem 5.6)

import Mathlib
import Definitions.Def_AlgMechDesign_NonOptimal_Model

open Finset

namespace AlgMechDesign.NonOptimal

/-- Claim 5.7 (Nisan–Ronen, p. 192). If the Compensation-and-Bonus mechanism based on `alloc` is
truthful, `t` is a positive type vector, `o` an optimal allocation for `t` and `M` at least every
entry of `t`, then replacing agent `i`'s type by `offOpt t o M i` (`tⁱ_j` on `oⁱ`, `M`
elsewhere) does not decrease the make-span of the allocation chosen by `alloc`. -/
theorem claim_5_7 {n k : ℕ} [NeZero n] (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (htruth : Truthful alloc) (t : Fin n → Fin k → ℝ) (ht : IsType t) (o : Fin k → Fin n)
    (ho : IsOptimalFor t o) (M : ℝ) (hM : ∀ i j, t i j ≤ M) (i : Fin n) :
    makespan t (alloc t) ≤
      makespan (Function.update t i (offOpt t o M i))
        (alloc (Function.update t i (offOpt t o M i))) := by sorry

end AlgMechDesign.NonOptimal
