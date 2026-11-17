-- Prove2me | Theorems.Thm_DepthOptQC_Synth_Supplement_theorem_9
-- name    : DepthOptQC.Synth.Supplement.theorem_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T00:47:46.71068+00:00
-- url     : https://prove2.me/theorems/d96b6156-98fd-469f-8b9f-8a6e241c3078
-- title:
--   Theorem 9 — $\Omega_{g,r}(\log\log(1/\varepsilon))$ depth lower bound for $R_z$ channels
-- statement:
--   Fix integers $g\ge1$ and $r\ge2$. There is a constant $c_{g,r}>0$ such that the following holds uniformly for every finite alphabet $G$ of at most $g$ unitary gates, each acting on at most $r$ qubits. For $0<\varepsilon\le1/16$, let $D_\varepsilon$ be the least depth at which, for every $\theta\in[0,2\pi)$, some circuit over $G$ with any number of clean ancillas and a designated output induces a channel $\mathcal E_C$ satisfying
--   $$
--   \|\mathcal E_C-\mathcal R_\theta\|_\diamond\le\varepsilon,
--   \qquad \mathcal R_\theta(\rho)=R_z(\theta)\rho R_z(\theta)^\dagger.
--   $$
--   If no such depth exists, set $D_\varepsilon=+\infty$. Then
--   $$
--   D_\varepsilon\ge c_{g,r}\log_2\log_2(1/\varepsilon).
--   $$
--
--   The bound shows that the base mission's doubly-logarithmic bounded-width synthesis depth is asymptotically optimal.
--
--   Differences from the source:
--   - encoding: $D_\varepsilon=+\infty$ when no depth works → `rotationDepth` is an `EReal` infimum whose empty value is $+\infty$; reason: this represents the paper's convention without a default natural number
--   - reading: $\Omega_{g,r}(\log\log(1/\varepsilon))$ → one positive constant chosen after $g,r$ but before $G$ and $\varepsilon$, with base-two logarithms; reason: this is the uniform meaning of the subscript and the logarithm base only rescales the constant
--   - encoding: $G$ is a set of quantum gates → `Gate.IsUnitary` is required for every member; reason: the shared `Gate` syntax does not bundle the paper's standing unitarity convention
-- source:
--   Vasconcelos, Depth-Optimal Quantum Compilation, arXiv:2609.34659, Theorem 9, p.28 (PDF p.30), Eqs. (118)–(121)

import Definitions.Def_DepthOptQC_Synth_Supplement_CircuitModel

set_option autoImplicit false

namespace DepthOptQC.Synth.Supplement

open QAlgorithms

/-- **Theorem 9 (Depth Lower-Bound)** — Vasconcelos, *Depth-Optimal Quantum Compilation*,
arXiv:2609.34659, p.28, Eqs. (118)–(121). Uniformly over every finite unitary gate alphabet of
cardinality at most `g` and arity at most `r`, the worst-case depth for diamond-norm approximation
of all `Rz` channels is `Ω_{g,r}(log log(1/ε))`. Arbitrarily many clean ancillas are allowed and
only the designated output is retained.

**Formalization Note.** `rotationDepth` is `+∞` when no depth works. The base-two logarithm fixes
an immaterial logarithm base. The positive constant is chosen after `g,r` but before the alphabet
and precision, which is the uniform meaning of the subscript `Ω_{g,r}`. -/
theorem theorem_9 :
    ∀ g r : ℕ, 1 ≤ g → 2 ≤ r → ∃ c : ℝ, 0 < c ∧
      ∀ G : Set Gate, G.Finite → G.ncard ≤ g → (∀ q ∈ G, q.IsUnitary) →
      (∀ q ∈ G, q.arity ≤ r) → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 16 →
        ((c * Real.logb 2 (Real.logb 2 (1 / ε)) : ℝ) : EReal) ≤ rotationDepth G ε := by sorry

end DepthOptQC.Synth.Supplement
