-- Prove2me | Theorems.Thm_CanadaCTP_Supplement_theorem_4
-- name    : CanadaCTP.Supplement.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T17:37:42.837203+00:00
-- url     : https://prove2.me/theorems/e09cd954-157a-4747-87b2-480308040340
-- title:
--   Theorem 4 — structure of simple optimal policies on Definition 10 instances
-- statement:
--   Consider an instance constructed as in Definition 10, a visiting order $\sigma$ of $\{0\}\cup[n]$ and a partition $(S,T)$ of $[n]$. If the simple policy $(\sigma,S)$ is an optimal adaptive policy, then
--
--   1. in $\sigma$, every path of $S$ is visited before every path of $T$;
--   2. in $\sigma$, the safe path comes last;
--   3. the ordering within each set is arbitrary: for every visiting order $\sigma'$ in which $S$ precedes $T$ and the safe path comes last, the simple policy $(\sigma',S)$ is optimal as well.
--
--   Together with the closed form of Theorem 5, this reduces optimality on these instances to the choice of the partition $(S,T)$, which is the core of the NP-hardness reduction of Theorem 6.
--
--   Differences from the source:
--   - encoding: paths 0 (safe) and 1, …, n; integers u_i, R → Fin (n+1), path 0 the safe path, path j.succ the paper's path j+1 for j : Fin n; u_i, R natural numbers; reason: Lean indexing; u_i ≥ 4 and R ≥ u_i − 1 ≥ 3 are positive, so the instances are the same
--   - encoding: a simple policy with visiting order σ and partition (S, T) (Definition 11) → Def10.simplePolicy σ S: deterministic, memory = position p in σ; at s it enters path σ p; at the middle vertex it traverses the second edge iff the path is safe, X_i = 0, or X_i = m_i and i ∉ S, else walks back to s (paying c_i) and moves to position p + 1; reason: Definition 11 fixes exactly the order, the m_i decisions, traversing 0 and never 3; a non-traversed path is left back to s and the next path of σ is entered, so the paper's simple policies are exactly these programs
--   - encoding: optimal adaptive policy (deterministic, history-dependent) → feasible randomized stateful policy with expCost = optCost (the published CanadaCTP.optCost); reason: the randomized stateful class contains the paper's policies and no mixture beats its best component, so the optimum and the optimal deterministic policies are the same
--   - reading: the ordering within each set is arbitrary → for every σ' with S before T and the safe path last, the simple policy (σ', S) is optimal; reason: the proof (p.24) shows that swapping adjacent paths of equal index leaves the cost unchanged, i.e. every such order is optimal
-- source:
--   Abels–Pitschmann–Schewior–Schmand, Canada Retravelled (manuscript, STOC 2027 submission, sha256 8117348eb78ba082edf376778214fa414f31cb0cd8a8d06c12a1dfba627e3a33), Theorem 4, p.24 (proof p.24)

import Mathlib
import Definitions.Def_CanadaCTP_Supplement_Def10
import Definitions.Def_CanadaCTP_Supplement_Optimal

namespace CanadaCTP.Supplement

open CanadaCTP

/-- Abels–Pitschmann–Schewior–Schmand, *Canada Retravelled* (manuscript, sha256 8117348e…3a33),
Theorem 4, p.24: "Every simple optimal policy for an instance constructed as in Definition 10 uses
a fixed visiting order σ in which S precedes T, the ordering within each set is arbitrary, and the
safe path comes last."

For every instance of Definition 10, every visiting order `σ` and every `S ⊆ [n]`: if the simple
policy `(σ, S)` is optimal (feasible with expected cost `E[Opt]`), then
1. in `σ`, `S` precedes `T = [n] \ S`;
2. in `σ`, the safe path comes last;
3. (the ordering within each set is arbitrary) for every visiting order `σ'` in which `S` precedes
   `T` and the safe path comes last, the simple policy `(σ', S)` is optimal too.

**Formalization Note.** The simple policy is `Def10.simplePolicy` (Definition 11), optimality is
`IsOptimal` against the published `CanadaCTP.optCost`, the safe path is path `0`. -/
theorem theorem_4 (D : Def10) (σ : Equiv.Perm (Fin (D.n + 1))) (S : Finset (Fin D.n))
    (hopt : IsOptimal D.inst (D.simplePolicy σ S)) :
    D.SPrecedesT σ S ∧ D.SafeLast σ ∧
      ∀ σ' : Equiv.Perm (Fin (D.n + 1)), D.SPrecedesT σ' S → D.SafeLast σ' →
        IsOptimal D.inst (D.simplePolicy σ' S) := by sorry

end CanadaCTP.Supplement
