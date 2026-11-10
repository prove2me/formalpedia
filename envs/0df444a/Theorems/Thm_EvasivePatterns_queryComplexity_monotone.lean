-- Prove2me | Theorems.Thm_EvasivePatterns_queryComplexity_monotone
-- name    : EvasivePatterns.queryComplexity_monotone
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:28:03.998475+00:00
-- url     : https://prove2.me/theorems/3342b23b-5a1a-40e6-afa9-f64cf8c9f739
-- title:
--   Proof of Theorem 1.1 (§6) — $D_P(n)$ is nondecreasing in $n$
-- statement:
--   For every binary pattern $P$ the query complexity $D_P(n)$ is nondecreasing in the text length:
--   $$
--   D_P(n) \le D_P(n+1) \qquad (n \ge 0).
--   $$
--   Appending a known bit opposite to the last symbol of $P$ creates no new occurrence, so a decision tree for length $n+1$ restricts to one for length $n$. In the proof of Theorem 1.1 this transfers the lower bound from multiples of $c$ to all lengths.
--
--   Differences from the source:
--   - generalization: binary pattern P (the paper's patterns have a smallest period, hence are nonempty) → any P : List Bool, the empty word included; reason: the statement also holds for the empty word, so it specializes to the source's claim for every nonempty P
-- source:
--   Faro, Marino, Pavone, A Complete Characterization of Eventually Evasive Binary Patterns, manuscript (Nov. 2026; sha256 e91deef3…), proof of Theorem 1.1, §6, p.9 (PDF p.10), lines 297–299

import Mathlib
import Definitions.Def_EvasivePatterns_queryComplexity

namespace EvasivePatterns

/-- **Monotonicity of `D_P`.** The depth `D_P(n)` is nondecreasing in `n`: appending a known bit
opposite to the last symbol of `P` creates no new occurrence, so any decision tree on the longer text
restricts to one on the shorter text.

Source: S. Faro, F. P. Marino, A. Pavone, *A Complete Characterization of Eventually Evasive Binary
Patterns*, manuscript (Nov. 2026), proof of Theorem 1.1, §6, printed p. 9 (PDF p. 10), lines 297–299 (unnumbered claim).

**Formalization Note** `P` is a binary word (`List Bool`); `D_P = queryComplexity P`. The empty word
(`D_P ≡ 0`) is not excluded. -/
theorem queryComplexity_monotone (P : List Bool) :
    Monotone (queryComplexity P) := by sorry

end EvasivePatterns
