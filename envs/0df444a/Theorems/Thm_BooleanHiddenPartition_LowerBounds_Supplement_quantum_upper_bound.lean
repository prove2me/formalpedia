-- Prove2me | Theorems.Thm_BooleanHiddenPartition_LowerBounds_Supplement_quantum_upper_bound
-- name    : BooleanHiddenPartition.LowerBounds.Supplement.quantum_upper_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T04:16:09.679967+00:00
-- url     : https://prove2.me/theorems/6d31085f-70b4-49f6-8bb8-c794f4bd4f51
-- title:
--   Theorem 13 — Unassisted quantum communication upper bound
-- statement:
--   Fix $\alpha\in(0,1)$ and an arity $k$. There is a constant $A=A(\alpha,k)>0$ such that the following holds for every admissible positive length $n$ and number of blocks $m$ with $km=\alpha n$. Let $f:\{\pm1\}^k\to\{\pm1\}$ have sign degree $d$, where $1\le d\le k$. For every $0<\varepsilon<1/2$, there exist a natural number $c$ and an unassisted one-way quantum strategy solving the full ordered-block $f$-BHP promise problem with success at least $1-\varepsilon$ on every promised input, and
--
--   $$c\le A(\alpha,k)\,n^{1-1/\lceil d/2\rceil}\log n\log(1/\varepsilon).$$
--
--   The constant is independent of $n,m,f,d,\varepsilon$, the input and the strategy. Messages are arbitrary mixed states on a space of dimension $2^c$, and Bob uses an arbitrary two-outcome measurement depending only on his input. This companion theorem supplies the quantum upper bound alongside the published lower-bound goal; it is not used in the proof of that goal.
--
--   **Formalization Note** There is no public random seed or prior entanglement. The natural-number ceiling is $(d+1)/2$, while the exponent is real. For $d=1$ and $d=2$ the exponent is exactly zero, so these cases are included with logarithmic communication. No sign-representing polynomial, symmetry, or balance assumption is imposed on $f$.
--
--   Differences from the source:
--   - encoding: sign-valued strings and ordered blocks with k dividing αn → the published Bool cube and Layout k n m α with km = αn; reason: true codes −1, coordinates are zero based, and all positive admissible layouts are preserved
--   - encoding: finite sign degree d → signDegree f = (d : WithTop ℕ); reason: the published least-degree definition represents the same finite degree
--   - encoding: O of the displayed communication expression with a fixed logarithm base → a positive existential multiplicative constant and natural logarithms; reason: changing a fixed logarithm base only rescales the permitted constant
--   - encoding: ceil(d/2) in the exponent → natural division (d + 1) / 2 followed by a cast to ℝ; reason: this is the exact ceiling for natural d; all exponent subtraction and inversion take place in ℝ
--   - encoding: a one-way quantum protocol sending c qubits → an unassisted QuantumStrategy on a 2^c-dimensional space; reason: mixed density states and two-outcome effects absorb private randomness and measurements; no public seed or shared entanglement is introduced
-- source:
--   Mark Bun, Joao F. Doriguello, John Kallaugher, Nadezhda Voronova, Characterizing Quantum Advantage for Generalizations of the Boolean Hidden Matching Problem, STOC 2027 submission #1085 (October 2026), p. 27, Theorem 13; proof pp. 27–30

import Definitions.Def_BooleanHiddenPartition_LowerBounds_Supplement_Error
import Definitions.Def_BooleanHiddenPartition_LowerBounds_SignDegree

set_option autoImplicit false

namespace BooleanHiddenPartition.LowerBounds.Supplement

/-- Theorem 13 (pp.27–30). The constant depends on α and k only.
Natural division (d + 1) / 2 is exactly ceil(d/2); exponent arithmetic is real. -/
theorem quantum_upper_bound :
    ∀ (α : ℝ) (k : ℕ), 0 < α → α < 1 →
      ∃ A : ℝ, 0 < A ∧
        ∀ (n m : ℕ) (L : Layout k n m α) (f : Cube k → Bool) (d : ℕ),
          1 ≤ d → d ≤ k → signDegree f = (d : WithTop ℕ) →
          ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
          ∃ (c : ℕ) (P : QuantumStrategy (Cube n) (BobInput n m) c),
            QuantumSolvesWithError L f P ε ∧
            (c : ℝ) ≤ A * ((n : ℝ) ^ (1 - 1 / (((d + 1) / 2 : ℕ) : ℝ)) *
              Real.log (n : ℝ) * Real.log (1 / ε)) := by sorry

end BooleanHiddenPartition.LowerBounds.Supplement
