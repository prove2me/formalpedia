-- Prove2me | Theorems.Thm_DepthOneQExp_theorem_2_11
-- name    : DepthOneQExp.theorem_2_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T02:47:43.092452+00:00
-- url     : https://prove2.me/theorems/e033c940-a103-4348-a1e8-8c61893298c9
-- title:
--   Theorem 2.11 (Kassabov): $K(\mathrm{SL}(3s;\mathbb F_2);\Sigma_{3s}) > 1/400$
-- statement:
--   For every integer $s\ge1$, the Kazhdan constant of $\mathrm{SL}(3s;\mathbb F_2)$ with respect to Kassabov's 14 generators $\Sigma_{3s}$ (Fact 2.10) satisfies
--   $$
--   K(\mathrm{SL}(3s;\mathbb F_2);\Sigma_{3s}) > \frac1{400}.
--   $$
--
--   This is the uniform-in-$s$ input that makes the expander's spectral gap independent of the number of qubits. It is [Kas07b, Theorem 8a], restated in the paper.
--
--   **Formalization Note** $\mathrm{SL}(3s;\mathbb F_2)$ carries Mathlib's discrete topology; $\Sigma_{3s}$ is the indexed family `sigma s`.
--
--   Differences from the source:
--   - encoding: the set Σ_{3s} of 14 matrices → the indexed family sigma s : Fin 14 → SL(3s; F₂); reason: the Kazhdan constant depends only on the set of values (the max over i), so multiplicity does not matter
--   - reading: K(SL(3s; F₂); Σ_{3s}) (definition deferred to [Kas07b]) → K over finite-dimensional unitary representations without nonzero invariant vectors; reason: for a finite group this equals the infimum over all unitary representations (cyclic subrepresentations are finite-dimensional)
-- source:
--   Anshu–Balasubramanian–Haferkamp–Harrow–Tan, Depth-1 expanders on the unitary group and applications, arXiv:2609.01605 (held version, sha256 3c3f8513…aebfd87), Theorem 2.11, Eq. (2.20), p.10 (cited from [Kas07b, Theorem 8a])

import Mathlib
import Definitions.Def_DepthOneQExp_sigma
import Definitions.Def_DepthOneQExp_kazhdan

namespace DepthOneQExp

/-- Theorem 2.11 ([Kas07b, Theorem 8a]) (Anshu–Balasubramanian–Haferkamp–Harrow–Tan, *Depth-1
expanders on the unitary group and applications*, arXiv:2609.01605, held version sha256
3c3f8513…aebfd87, Theorem 2.11, Eq. (2.20), p.10): for every integer `s ≥ 1`, the Kazhdan constant
of `SL(3s; 𝔽₂)` with respect to Kassabov's 14 generators `Σ_{3s}` exceeds `1/400`.

**Formalization Note** `SL(3s; 𝔽₂)` carries Mathlib's discrete topology; `Σ_{3s}` is the indexed
family `sigma s`; `K` is `kazhdan`. -/
theorem theorem_2_11 (s : ℕ) (hs : 1 ≤ s) :
    (1 / 400 : ℝ) < kazhdan (Matrix.SpecialLinearGroup (Fin (3 * s)) (ZMod 2)) (sigma s) := by sorry

end DepthOneQExp
