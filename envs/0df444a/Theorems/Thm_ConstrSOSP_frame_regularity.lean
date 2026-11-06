-- Prove2me | Theorems.Thm_ConstrSOSP_frame_regularity
-- name    : ConstrSOSP.frame_regularity
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:08:15.111724+00:00
-- url     : https://prove2.me/theorems/6811b5c8-78a5-48b0-b507-de7cd51ea9e1
-- title:
--   The normalized $F$ has constants $5/(256N^2)$, $25/(128N)$, $125/128$
-- statement:
--   Let $C$ be a well-formed Iter circuit, $N=6\cdot2^n+6$ and $F(z)=\bar f(Sz-m(1,1))/(c_0N^4)$ the normalized framed function.
--
--   **Theorem.** $F$ is $C^2$, and for all $z,z'\in[0,1]^2$
--   $$
--   |F(z)-F(z')|\le\frac5{256N^2}\|z-z'\|,\qquad \|\nabla F(z)-\nabla F(z')\|\le\frac{25}{128N}\|z-z'\|,
--   $$
--   $$
--   \|\nabla^2F(z)-\nabla^2F(z')\|_F\le\frac{125}{128}\|z-z'\| .
--   $$
--
--   All three constants are below $1$, which is what makes the regularity promises with $L=L_1=L_2=1$ hold.
--
--   Differences from the source:
--   - reading: ‖∇²f(x) − ∇²f(y)‖ with an unspecified matrix norm (Definitions 4.6, 4.8, 4.10) → Frobenius norm; reason: the norm of the proof of Lemma 5.4 ("Throughout the proof, matrix norms are Frobenius norms", p.49); it bounds the spectral norm, so the promise is the stronger one
--   - encoding: ∇f, ∇²f of the C² function → Mathlib Fréchet derivatives (gradVec, hessMat); vector norms written out as Euclidean norms; reason: Lean convention; same values for C² functions
--   - generalization: F twice continuously differentiable on [0, 1]² (as f_sc, p.54) → C² on all of ℝ² for the Lean function, which continues the boundary cells' polynomials outside the framed square; reason: specializes to the paper's claim on a neighbourhood of [0, 1]²
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), proof of Corollary 5.6, p.56

import Mathlib
import Definitions.Def_ConstrSOSP_Circuit_WF
import Definitions.Def_ConstrSOSP_gridN
import Definitions.Def_ConstrSOSP_Fnorm
import Definitions.Def_ConstrSOSP_Poly
import Definitions.Def_ConstrSOSP_boxA
import Definitions.Def_ConstrSOSP_boxB
import Definitions.Def_ApproxVI_euclNorm
import Definitions.Def_ParamSDPTraj_frob
import Definitions.Def_ConstrSOSP_gradVec
import Definitions.Def_ConstrSOSP_hessMat

namespace ConstrSOSP

/-- **Regularity of the normalized function `F`** (arXiv:2604.02285, 2 Nov 2026, proof of
Corollary 5.6, p.56: "Since N ≤ S ≤ 5N/4, its Lipschitz, smoothness, and Hessian-Lipschitz
constants are bounded respectively by 5/(256N^2), 25/(128N), 125/128, and hence are all less
than 1.").

For every well-formed Iter circuit `C` with `N = 6·2ⁿ + 6`, the normalized function
`F(z) = f̄(Sz − m(1, 1))/(c₀N⁴)` (`Fnorm`) is `C²`, and for all `z, z' ∈ [0, 1]²`:
`|F(z) − F(z')| ≤ 5/(256N²) ‖z − z'‖`, `‖∇F(z) − ∇F(z')‖ ≤ 25/(128N) ‖z − z'‖`,
`‖∇²F(z) − ∇²F(z')‖_F ≤ 125/128 ‖z − z'‖`.

**Formalization Note** Euclidean vector norms; Frobenius norm for the Hessian difference. -/
theorem frame_regularity (C : Circuit) (hC : C.WF) :
    ContDiff ℝ 2 (Fnorm C) ∧
      ∀ z z' : Fin 2 → ℝ, z ∈ Poly boxA boxB → z' ∈ Poly boxA boxB →
        |Fnorm C z - Fnorm C z'| ≤ 5 / (256 * (gridN C.n : ℝ) ^ 2) * ApproxVI.euclNorm (z - z') ∧
        ApproxVI.euclNorm (gradVec (Fnorm C) z - gradVec (Fnorm C) z') ≤
          25 / (128 * (gridN C.n : ℝ)) * ApproxVI.euclNorm (z - z') ∧
        ParamSDPTraj.frob (hessMat (Fnorm C) z - hessMat (Fnorm C) z') ≤ 125 / 128 * ApproxVI.euclNorm (z - z') := by sorry

end ConstrSOSP
