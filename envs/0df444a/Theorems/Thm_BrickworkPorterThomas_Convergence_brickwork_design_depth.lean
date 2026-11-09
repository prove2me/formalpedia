-- Prove2me | Theorems.Thm_BrickworkPorterThomas_Convergence_brickwork_design_depth
-- name    : BrickworkPorterThomas.Convergence.brickwork_design_depth
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:16:19.967959+00:00
-- url     : https://prove2.me/theorems/45044dea-4cce-4a70-a4e2-54d55f620896
-- title:
--   Theorem 2.5 — brickwork circuits of depth $C(nk+\log(1/\varepsilon))$ are $\varepsilon$-approximate $k$-designs
-- statement:
--   There is an absolute constant $C>0$ such that, for every even $n\ge2$, every $k\ge1$ and every $0<\varepsilon<1$, if
--
--   $$
--   l\ge C\left(nk+\log(1/\varepsilon)\right),
--   $$
--
--   then the depth-$l$ brickwork Haar random circuit ensemble $\mathcal C(l)$ on $n$ qubits is an additive $\varepsilon$-approximate unitary $k$-design, that is, $\|\mathcal M^{(k)}_{\mathcal C(l)}-\mathcal M^{(k)}_{\mu_H}\|_\diamond\le\varepsilon$.
--
--   This result is cited from [BH26]. With $\varepsilon=d^{-k}$ it shows that depth $O(nk)$ gives the design property assumed in Theorem 1.1, and it converts the design order $k=\Theta(n^{2m}\log n)$ into the depth $\Theta(n^{2m+1}\log n)$.
--
--   **Formalization Note** The constant $C$ is uniform in $n,k,\varepsilon$. Depth counts individual parallel layers.
--
--   Differences from the source:
--
--   - encoding: n even, qubits 1..n on a ring, d = 2^n → n = 2M with M ≥ 1, qubits Fin (2M) (0-based), d = 2^(2M); reason: Definition 2.4 assumes n even; every even n ≥ 2 is some 2M; relabelling only
--   - encoding: layers numbered 1..l, odd layers on (1,2),(3,4),…, even layers on (2,3),…,(n,1) → layers numbered 0..l−1 with the pairs of the reused brickPair (Lean layer j is the source layer j+1); reason: index shift only; the pairs and the chronological order are the source’s
--   - encoding: a law ν on SU(d) (Definition 2.3) → a law on d×d complex matrices supported on SU(d) (Borel σ-algebra of the matrix space); reason: the twirl and the output probability only depend on the pushed-forward law; same instances
--   - encoding: diamond norm of M_ν^(k) − M_μH^(k) on the k-fold system → the reused stabilized trace-norm diamond norm, after relabelling the basis of the k-fold system (k-tuples of bitstrings) by Fin(d^k); reason: a basis relabelling is a unitary permutation and changes no trace norm
-- source:
--   Aniruddha Sen, Nick Hunter-Jones, STOC 2027 submission #118 (October 2026), §2, p. 5, Theorem 2.5, Eq. (11); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/118.pdf (SHA-256 8c25edf56b45d2ace15e9e3c1f1b40a88b30e3391593a8c4cdfc212e1544c326)

import Mathlib
import Definitions.Def_BrickworkPorterThomas_Convergence_Circuit

namespace BrickworkPorterThomas.Convergence

/-- Theorem 2.5 (p. 5, cited from [BH26]). There is an absolute constant `C > 0` such that for
every number `n = 2M` of qubits, every `k ≥ 1` and every `0 < ε < 1`, if
`l ≥ C (n k + log(1/ε))` then the depth-`l` brickwork ensemble `C(l)` is an additive
`ε`-approximate unitary `k`-design. -/
theorem brickwork_design_depth : ∃ C : ℝ, 0 < C ∧
    ∀ (M k l : ℕ) (ε : ℝ), 1 ≤ M → 1 ≤ k → 0 < ε → ε < 1 →
      C * (((2 * M : ℕ) : ℝ) * k + Real.log (1 / ε)) ≤ l →
      IsApproxDesign (circuitLaw M l) k ε := by sorry

end BrickworkPorterThomas.Convergence
