-- Prove2me | Theorems.Thm_AggCG_arrangement_faces
-- name    : AggCG.arrangement_faces
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:06:30.358381+00:00
-- url     : https://prove2.me/theorems/2b9a6ab2-cd4c-472e-aa42-ab87acb55147
-- title:
--   Proof of Proposition I.4 — the arrangement count
-- statement:
--   There is an absolute constant $C>0$ such that for all $m,H\ge 1$ and all affine forms $h_1,\dots,h_H$ on $\mathbb R^m$, the number of sign vectors
--   $$(\operatorname{sign}h_1(x),\dots,\operatorname{sign}h_H(x))\in\{-,0,+\}^H,\quad x\in\mathbb R^m,$$
--   is at most $(CH)^m$. Faces of all dimensions of the arrangement are these sign vectors.
--
--   The paper uses it, without a citation, on $O(N)$ hyperplanes.
--
--   **Formalization Note** No general position hypothesis; zero and repeated forms are allowed.
--
--   Differences from the source:
--   - generalization: "For N inputs, there are O(N) such hyperplanes and at most (CN)^m arrangement faces" → any H ≥ 1 affine forms on ℝ^m, at most (CH)^m sign vectors; reason: with H = O(N) this gives (C′N)^m, the source's claim on its critical hyperplanes
-- source:
--   Sharma, Computational Complexity of Data-Driven Configuration for Integer Programming, Clustering, and Learning Algorithms, STOC 2027 submission (manuscript sha256 f7ea0248…), proof of Proposition I.4, p.52 (PDF p.53)

import Mathlib

namespace AggCG

/-- **The arrangement count** (Sharma, *Computational Complexity of Data-Driven Configuration for Integer Programming, Clustering, and Learning Algorithms*, STOC 2027 submission (manuscript sha256 f7ea0248…), proof of Proposition I.4, p.52, PDF p.53: "at most (CN)^m arrangement faces of all dimensions, for an absolute C"): there is an absolute `C` such that any `H ≥ 1` affine forms on `ℝ^m` have at most `(CH)^m` sign vectors. Faces of all dimensions are the sign vectors (with values `−, 0, +`).

**Formalization Note** Arbitrary affine forms, with no general position hypothesis and with zero or repeated forms allowed. The source's `O(N)` hyperplanes for `N` inputs are the case `H = O(N)`. -/
theorem arrangement_faces :
    ∃ C : ℝ, 0 < C ∧ ∀ (m H : ℕ), 1 ≤ m → 1 ≤ H →
      ∀ (a : Fin H → Fin m → ℝ) (b : Fin H → ℝ),
        (({s : Fin H → SignType | ∃ x : Fin m → ℝ, ∀ i, s i = SignType.sign (∑ j, a i j * x j + b i)}).ncard : ℝ)
          ≤ (C * H) ^ m := by sorry

end AggCG
