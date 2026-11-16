-- Prove2me | Theorems.Thm_DetCCHard_Supplement_theorem_1_2
-- name    : DetCCHard.Supplement.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:56:34.507699+00:00
-- url     : https://prove2.me/theorems/fcf7b56c-116e-4bb7-9922-1ae721509d2e
-- title:
--   Theorem 1.2 — for every fixed $k$, 3-SAT reduces in polynomial time to tables with $D^{\mathrm{alt}}_A(M) \le B$ or $D^{\mathrm{alt}}_A(M) \ge B + k$
-- statement:
--   For every fixed integer $k \ge 1$, a deterministic polynomial-time algorithm maps a 3-CNF formula $\Phi$ to an explicit total Boolean table $M$ and an integer $B$ such that
--   $$
--   \Phi \in \mathrm{SAT} \implies D^{\mathrm{alt}}_A(M) \le B, \qquad \Phi \notin \mathrm{SAT} \implies D^{\mathrm{alt}}_A(M) \ge B + k .
--   $$
--   Here $D^{\mathrm{alt}}_A$ is the deterministic communication cost under strict alternation with Alice speaking first, public output and every bit charged. The polynomial bounds on output size and running time may depend on $k$.
--
--   With a gap larger than twice the additive error, an estimator of the alternating cost would decide 3-SAT; this settles Yao's question for his original speaking order.
--
--   **Formalization Note** The algorithm is a string function, polynomial-time in the sense of the published `CookPvsNP.PolyTimeComputable` (whose time bound also bounds the output length), chosen after $k$. Its output is exactly the encoding of an $a \times b$ table with $a, b \ge 1$ and of $B$.
--
--   Differences from the source:
--   - generalization: 3-CNF formula (three literals per clause) → every clause has at most three literals; reason: formulas with exactly three literals per clause are a special case
--   - encoding: 3-CNF formulas as input strings (format unspecified) → the published CookPvsNP.encodeCNF, variable indices in unary; reason: renaming variables to 0, …, N−1 is polynomial-time, so unary and binary encodings are interconvertible in polynomial time
--   - encoding: an integer B → B a natural number, written in binary; reason: a negative B certifies unsatisfiability (D^alt_A(M) ≥ 0), and a fixed table of alternating cost at least k with B = 0 can be output instead, so both readings are equivalent
--   - encoding: an explicit total Boolean table (Definition 4.1: finite nonempty input sets) → the string encodeTableNat M B of an a × b table with a, b ≥ 1; reason: an explicit injective encoding; the paper fixes no format
--   - encoding: D^alt_A: strict alternation, Alice first, public output, every bit charged → DaltA, the least depth of a published protocol tree satisfying AltFrom true; reason: strict alternation from Alice is exactly the condition that Alice and Bob nodes alternate along every path starting with Alice; leaves make stopping public
-- source:
--   Gaspers–He–Mackenzie, NP-Hardness and Additive Inapproximability of Deterministic Communication Complexity, arXiv:2508.05597 (held version, sha256 ad552d13…), Theorem 1.2, p.3 (proof on p.48)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_DetCCHard_CodeSym
import Definitions.Def_DetCCHard_Is3CNF
import Definitions.Def_DetCCHard_Supplement_DaltA

namespace DetCCHard.Supplement

open DetCCHard

/-- **Theorem 1.2 (Fixed gaps under strict alternation)** (Gaspers–He–Mackenzie, arXiv:2508.05597, held version sha256 ad552d13…a4a03, Theorem 1.2, p.3). For every fixed
integer `k ≥ 1`, a deterministic polynomial-time algorithm maps a 3-CNF formula `Φ` to an explicit
total Boolean table `M` and an integer `B` such that `Φ ∈ SAT ⟹ D^alt_A(M) ≤ B` and
`Φ ∉ SAT ⟹ D^alt_A(M) ≥ B + k`. The polynomial bounds on output size and running time may depend
on `k`.

**Formalization Note** The algorithm is a string function, polynomial-time in the sense of the
published `CookPvsNP.PolyTimeComputable` (which bounds the output length too), chosen after `k`. Its
input is the published CNF encoding (variable indices in unary) and its output is
`encodeTableNat M B`, the explicit encoding of an `a × b` table with nonempty input sets
(Definition 4.1) and of `B` in binary. `D^alt_A` is `DaltA`: strict alternation, Alice first,
public output, every bit charged. A 3-CNF formula has at most three literals per clause. -/
theorem theorem_1_2 :
    ∀ k : ℕ, 1 ≤ k →
      ∃ f : List CookPvsNP.SatSym → List CodeSym, CookPvsNP.PolyTimeComputable f ∧
        ∀ Φ : CookPvsNP.CNF, Is3CNF Φ →
          ∃ (a b : ℕ) (M : Fin a → Fin b → Bool) (B : ℕ), 0 < a ∧ 0 < b ∧
            f (CookPvsNP.encodeCNF Φ) = encodeTableNat M B ∧
              (Φ.Satisfiable → DaltA M ≤ B) ∧ (¬ Φ.Satisfiable → B + k ≤ DaltA M) := by sorry

end DetCCHard.Supplement
