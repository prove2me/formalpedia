-- Prove2me | Theorems.Thm_AlgMechDesign_LowerBound_ratio_step_even
-- name    : AlgMechDesign.LowerBound.ratio_step_even
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T18:55:30.077706+00:00
-- url     : https://prove2.me/theorems/d2ea082e-4288-465a-b3cf-3b3a622a2a43
-- title:
--   Proof of Theorem 4.6, even case — make-span $|x^2|$ against $\tfrac12|x^2| + k\varepsilon$
-- statement:
--   In the setting of Claim 4.8 (two agents, $k\ge3$ tasks, a truthful direct mechanism $(x,p)$, $t \equiv 1$ with $|x^1(t)|\le|x^2(t)|$, $x = x^1(t)$, $0<\varepsilon<1$ and $\hat t = t(x\xrightarrow{1}\varepsilon,\ \bar x\xrightarrow{1}1+\varepsilon)$), assume that $|x^2(t)|$ is even. Then the mechanism's make-span at $\hat t$ equals $|x^2(t)|$, while some allocation $y$ does much better:
--
--   $$
--   g\big(x(\hat t),\hat t\big) = |x^2(t)| \qquad\text{and}\qquad g(y,\hat t) \le \tfrac12\,|x^2(t)| + k\,\varepsilon .
--   $$
--
--   (The allocation meant is the one giving agent 1, in addition to $x^1(t)$, half of agent 2's original tasks.) Letting $\varepsilon \to 0$ this gives the ratio $2$ in the lower bound.
--
--   **Formalization Note** Agents 1 and 2 are `0` and `1` in `Fin 2`. The good allocation $y$ is existentially quantified. The odd case of the paper's proof is not part of this statement.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games Econ. Behav. 35, 2001, p. 179, proof of Theorem 4.6, paragraph after Claim 4.8

import Mathlib
import Definitions.Def_AlgMechDesign_LowerBound_Model

namespace AlgMechDesign.LowerBound

/-- The ratio step of the proof of Theorem 4.6 (even case): in the setting of Claim 4.8, if
`|x²(t)|` is even then at `t̂` the mechanism's make-span is `|x²(t)|`, while some allocation has
make-span at most `|x²(t)|/2 + k·ε`. -/
theorem ratio_step_even {k : ℕ} (hk : 3 ≤ k) (alloc : (Fin 2 → Fin k → ℝ) → (Fin k → Fin 2))
    (pay : (Fin 2 → Fin k → ℝ) → Fin 2 → ℝ) (htruth : IsTruthful alloc pay)
    (t : Fin 2 → Fin k → ℝ) (ht : t = fun _ _ => 1)
    (hcard : (taskSet (alloc t) 0).card ≤ (taskSet (alloc t) 1).card)
    (heven : Even (taskSet (alloc t) 1).card)
    (x : Finset (Fin k)) (hx : x = taskSet (alloc t) 0)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (that : Fin 2 → Fin k → ℝ)
    (hthat : that = Function.update t 0 (fun j => if j ∈ x then ε else 1 + ε)) :
    makespan that (alloc that) = ((taskSet (alloc t) 1).card : ℝ) ∧
      ∃ y : Fin k → Fin 2,
        makespan that y ≤ ((taskSet (alloc t) 1).card : ℝ) / 2 + (k : ℝ) * ε := by sorry

end AlgMechDesign.LowerBound
