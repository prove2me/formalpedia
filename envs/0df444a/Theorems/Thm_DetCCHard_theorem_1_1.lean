-- Prove2me | Theorems.Thm_DetCCHard_theorem_1_1
-- name    : DetCCHard.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:36:49.691195+00:00
-- url     : https://prove2.me/theorems/6e9d0716-a30e-4b8c-886f-4959bc3bf3dd
-- title:
--   Theorem 1.1 — for every fixed $k$, 3-SAT reduces in polynomial time to tables with $D(M) \le B$ or $D(M) \ge B + k$
-- statement:
--   For every fixed integer $k \ge 1$, a deterministic polynomial-time algorithm maps a 3-CNF formula $\Phi$ to an explicit total Boolean table $M$ and an integer $B$ such that
--   $$
--   \Phi \in \mathrm{SAT} \implies D(M) \le B, \qquad \Phi \notin \mathrm{SAT} \implies D(M) \ge B + k .
--   $$
--   The polynomial may depend on $k$. The table can be taken square with power-of-two side length.
--
--   Consequently, for every fixed additive error, estimating the deterministic communication complexity of an explicitly given table in deterministic polynomial time implies $\mathrm P = \mathrm{NP}$.
--
--   **Formalization Note** The algorithm is a string function, polynomial-time in the sense of the published `CookPvsNP.PolyTimeComputable` and chosen after $k$. Its output is exactly the encoding of the $2^j \times 2^j$ table and of $B$; $D$ is the deterministic communication complexity with unrestricted speaking order.
--
--   Differences from the source:
--   - generalization: 3-CNF formula (three literals per clause) → every clause has at most three literals; reason: formulas with exactly three literals per clause are a special case
--   - encoding: 3-CNF formulas as input strings (format unspecified) → the published CookPvsNP.encodeCNF, variable indices in unary; reason: renaming variables to 0, …, N−1 is polynomial-time, so unary and binary encodings are interconvertible in polynomial time
--   - encoding: an integer B → B a natural number, written in binary; reason: the paper's B is d_{0,g} + k h_g ≥ 0; in general a negative B certifies unsatisfiability (D(M) ≥ 0), and a fixed table of cost at least k with B = 0 can be output instead, so both readings are equivalent
--   - encoding: an explicit total Boolean table → the string encodeTableNat M B (header [2^j, 2^j, B], then the rows); reason: an explicit injective encoding; the paper fixes no format
-- source:
--   Gaspers–He–Mackenzie, NP-Hardness and Additive Inapproximability of Deterministic Communication Complexity, arXiv:2508.05597 (held version, sha256 ad552d13…), Theorem 1.1, p.3 (proof on p.37)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_DetCCHard_commCost
import Definitions.Def_DetCCHard_CodeSym
import Definitions.Def_DetCCHard_Is3CNF

namespace DetCCHard

/-- **Theorem 1.1 (Fixed gaps for unrestricted protocols)** (Gaspers–He–Mackenzie,
arXiv:2508.05597, held version sha256 ad552d13…a4a03, Theorem 1.1, p.3). For every fixed integer
`k ≥ 1`, a deterministic polynomial-time algorithm maps a 3-CNF formula `Φ` to an explicit total
Boolean table `M` and an integer `B` such that `Φ ∈ SAT ⟹ D(M) ≤ B` and
`Φ ∉ SAT ⟹ D(M) ≥ B + k`. The polynomial may depend on `k`. The table can be taken square with
power-of-two side length.

**Formalization Note** The algorithm is a string function, polynomial-time in the sense of the
published `CookPvsNP.PolyTimeComputable` (Cook's one-tape machine, time `|x|^c + c`), chosen
after `k`; its input is the published CNF encoding (variable indices in unary) and its output *is*
`encodeTableNat M B`, the explicit encoding of the `2^j × 2^j` table and of `B` in binary. A 3-CNF
formula has at most three literals per clause. `D` is `Dcost`, the deterministic communication
complexity with unrestricted speaking order. -/
theorem theorem_1_1 :
    ∀ k : ℕ, 1 ≤ k →
      ∃ f : List CookPvsNP.SatSym → List CodeSym, CookPvsNP.PolyTimeComputable f ∧
        ∀ Φ : CookPvsNP.CNF, Is3CNF Φ →
          ∃ (j : ℕ) (M : Fin (2 ^ j) → Fin (2 ^ j) → Bool) (B : ℕ),
            f (CookPvsNP.encodeCNF Φ) = encodeTableNat M B ∧
              (Φ.Satisfiable → Dcost M ≤ B) ∧ (¬ Φ.Satisfiable → B + k ≤ Dcost M) := by sorry

end DetCCHard
