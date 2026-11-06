-- Prove2me | Theorems.Thm_ConstrSOSP_lemma_5_4
-- name    : ConstrSOSP.lemma_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:07:30.607422+00:00
-- url     : https://prove2.me/theorems/b933cfa2-4393-42d3-8310-b15753494af5
-- title:
--   Lemma 5.4: $f$ is $2^{70}N$-Lipschitz, $2^{73}N$-smooth and $2^{75}N$-Hessian-Lipschitz
-- statement:
--   Let $C$ be a well-formed Iter circuit, $N=6\cdot2^n+6$ and $f$ the constructed function.
--
--   **Theorem.** For all $z,z'\in[0,N]^2$,
--   $$
--   |f(z)-f(z')|\le2^{70}N\|z-z'\|,\qquad \|\nabla f(z)-\nabla f(z')\|\le2^{73}N\|z-z'\|,
--   $$
--   $$
--   \|\nabla^2f(z)-\nabla^2f(z')\|_F\le2^{75}N\|z-z'\| .
--   $$
--
--   These bounds, divided by the normalization $c_0N^4$, give the unit constants of the final instance.
--
--   Differences from the source:
--   - reading: ‖∇²f(x) − ∇²f(y)‖ with an unspecified matrix norm (Definitions 4.6, 4.8, 4.10) → Frobenius norm; reason: the norm of the proof of Lemma 5.4 ("Throughout the proof, matrix norms are Frobenius norms", p.49); it bounds the spectral norm, so the promise is the stronger one
--   - encoding: ∇f, ∇²f of the C² function → Mathlib Fréchet derivatives (gradVec, hessMat); vector norms written out as Euclidean norms; reason: Lean convention; same values for C² functions
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), Lemma 5.4, p.49 (proof pp.49–51)

import Mathlib
import Definitions.Def_ConstrSOSP_Circuit_WF
import Definitions.Def_ConstrSOSP_gridN
import Definitions.Def_ConstrSOSP_fGrid
import Definitions.Def_ApproxVI_euclNorm
import Definitions.Def_ParamSDPTraj_frob
import Definitions.Def_ConstrSOSP_gradVec
import Definitions.Def_ConstrSOSP_hessMat

namespace ConstrSOSP

/-- **Lemma 5.4** (arXiv:2604.02285, 2 Nov 2026, p.49): "The constructed function f is
L-Lipschitz, L1-smooth and L2-Hessian Lipschitz on [0, N]^2, with L ≤ 2^70 N, L1 ≤ 2^73 N and
L2 ≤ 2^75 N."

For every well-formed Iter circuit `C`, `N = 6·2ⁿ + 6` and `f = fGrid C`, for all
`z, z' ∈ [0, N]²`:
`|f(z) − f(z')| ≤ 2⁷⁰N ‖z − z'‖`, `‖∇f(z) − ∇f(z')‖ ≤ 2⁷³N ‖z − z'‖` and
`‖∇²f(z) − ∇²f(z')‖_F ≤ 2⁷⁵N ‖z − z'‖`.

**Formalization Note** Vector norms are Euclidean; the Hessian difference is measured in the
Frobenius norm, as in the proof ("Throughout the proof, matrix norms are Frobenius norms", p.49),
which bounds the spectral norm. -/
theorem lemma_5_4 (C : Circuit) (hC : C.WF) (z z' : Fin 2 → ℝ)
    (hz : ∀ i, 0 ≤ z i ∧ z i ≤ (gridN C.n : ℝ)) (hz' : ∀ i, 0 ≤ z' i ∧ z' i ≤ (gridN C.n : ℝ)) :
    |fGrid C z - fGrid C z'| ≤ 2 ^ 70 * (gridN C.n : ℝ) * ApproxVI.euclNorm (z - z') ∧
      ApproxVI.euclNorm (gradVec (fGrid C) z - gradVec (fGrid C) z') ≤ 2 ^ 73 * (gridN C.n : ℝ) * ApproxVI.euclNorm (z - z') ∧
      ParamSDPTraj.frob (hessMat (fGrid C) z - hessMat (fGrid C) z') ≤
        2 ^ 75 * (gridN C.n : ℝ) * ApproxVI.euclNorm (z - z') := by sorry

end ConstrSOSP
