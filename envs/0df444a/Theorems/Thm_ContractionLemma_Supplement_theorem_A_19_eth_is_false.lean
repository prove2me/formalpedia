-- Prove2me | Theorems.Thm_ContractionLemma_Supplement_theorem_A_19_eth_is_false
-- name    : ContractionLemma.Supplement.theorem_A_19_eth_is_false
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:31:05.567795+00:00
-- url     : https://prove2.me/theorems/651fab63-5a80-40da-b131-876aae5100b3
-- title:
--   Theorem A.19, p.78 — counting 3-CNF solutions in time $2^{\varepsilon n}\mathrm{poly}(|\varphi|)$ for every $\varepsilon>0$; ETH is false
-- statement:
--   1. For every $\varepsilon>0$ there is a deterministic algorithm that, given a 3-CNF formula $\varphi$ on $n$ variables, counts its satisfying assignments in time $2^{\varepsilon n}\,\mathrm{poly}(|\varphi|)$ and polynomial space, i.e. in time $C\,2^{\varepsilon n}(|\varphi|+1)^C$ and space $C(|\varphi|+1)^C$ with $C$ depending only on $\varepsilon$.
--   2. In particular, the Exponential Time Hypothesis is false: for every $\delta>0$ satisfiability of 3-CNF formulas on $n$ variables can be decided in time $2^{\delta n}\,\mathrm{poly}(|\varphi|)$.
--
--   The algorithm uses Theorem A.2 only as a black box, after sparsification.
--
--   Differences from the source:
--   - reading: no space bound in the theorem sentence → space at most $C(L+1)^C$ (polynomial in the input length); reason: the paper's convention, p.3: "all algorithms are deterministic and use polynomial space unless we say otherwise"
--   - encoding: 3-CNF formulas and $|\varphi|$ → published SubexponentialSAT CNFs with clauses of at most three literals; $|\varphi|$ the length of their published encoding; reason: reuse of the platform's formula encoding
-- source:
--   Gajulapalli, The Contraction Lemma Beyond ETH (manuscript, sha256 049caea1…), Theorem A.19 and App. A.7, p.78; proof p.80

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_ContractionLemma_RunsWithin
import Definitions.Def_ContractionLemma_Supplement_Common

set_option autoImplicit false

namespace ContractionLemma.Supplement

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- **Theorem A.19** — Gajulapalli, *The Contraction Lemma Beyond ETH* (manuscript, sha256
049caea1…), p.78 (PDF p.81).

"For every `ε > 0` there is a deterministic algorithm that, given a 3-CNF formula `φ` on `n`
variables, counts its satisfying assignments in time `2^{εn} poly(|φ|)`. In particular, ETH is
false."

1. For every real `ε > 0` there are a machine `A` and a constant `C` such that for every CNF `φ` on
   `n` variables with clauses of at most three literals, `A` outputs the number of satisfying
   assignments of `φ` in time `C 2^{εn} (|φ|+1)^C` and space `C (|φ|+1)^C`.
2. ETH (App. A.7, p.78) is false.

**Formalization Note.** Formulas and their encodings are those of the published `SubexponentialSAT`
definitions; `|φ|` is the length of `encodeCNF φ`. The polynomial-space clause is the paper's
convention (p.3): the proof runs sparsification and Theorem A.2 one after another. -/
theorem theorem_A_19_eth_is_false :
    (∀ ε : ℝ, 0 < ε → ∃ (A : PrimitiveMachine) (out : Fin A.tapeCount) (C : ℕ),
      ∀ (n : ℕ) (F : SAT.CNF (Fin n)), SAT.WidthAtMost 3 F →
        ContractionLemma.RunsWithin A out (Encoding.encodeCNF F) (countWord (SAT.count F))
          (C * (2 : ℝ) ^ (ε * n) * ((Encoding.formulaBitLength F : ℝ) + 1) ^ C)
          (C * ((Encoding.formulaBitLength F : ℝ) + 1) ^ C)) ∧
    ¬ ETH := by sorry

end ContractionLemma.Supplement
