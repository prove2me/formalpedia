-- Prove2me | Theorems.Thm_ConstrSOSP_frame_kkt_margin
-- name    : ConstrSOSP.frame_kkt_margin
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:08:42.1321+00:00
-- url     : https://prove2.me/theorems/131ef6a6-6384-43da-868e-b922c16e2492
-- title:
--   Every $\epsilon$-approximate KKT point of $F$ lies in $[1/12,11/12]^2$
-- statement:
--   Let $C$ be a well-formed Iter circuit with $N=6\cdot2^n+6\ge40$, $F$ the normalized function and $\epsilon=\epsilon_0^2/(c_0^2N^4)$.
--
--   **Theorem.** Every $z\in[0,1]^2$ with $\|g_\pi(z)\|\le\epsilon$ (proximal gradient of $F$ on $[0,1]^2$ with smoothness constant $1$) lies in $[1/12,11/12]^2$.
--
--   The frame added around $[0,N]^2$ pushes every approximate KKT point at least $m/S\ge1/12$ away from the boundary; this is the KKT-margin promise of Theorem 5.1.
--
--   Differences from the source:
--   - encoding: ∇f, ∇²f of the C² function → Mathlib Fréchet derivatives (gradVec, hessMat); vector norms written out as Euclidean norms; reason: Lean convention; same values for C² functions
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), proof of Corollary 5.6, p.56

import Mathlib
import Definitions.Def_ConstrSOSP_Circuit_WF
import Definitions.Def_ConstrSOSP_gridN
import Definitions.Def_ConstrSOSP_Fnorm
import Definitions.Def_ConstrSOSP_epsF
import Definitions.Def_ConstrSOSP_boxA
import Definitions.Def_ConstrSOSP_boxB
import Definitions.Def_ConstrSOSP_IsApproxKKT
import Definitions.Def_ConstrSOSP_gradVec

namespace ConstrSOSP

/-- **Every ϵ-approximate KKT point of `F` is `1/12` away from the boundary** (arXiv:2604.02285,
2 Nov 2026, proof of Corollary 5.6, p.56: "Every ϵ-approximate KKT point consequently maps into
(0, N)^2 and has distance at least m/S ≥ 1/12 from the boundary of [0, 1]^2; here N ≥ 40
suffices.").

For every well-formed Iter circuit `C` with `N = 6·2ⁿ + 6 ≥ 40` and `ϵ = ϵ₀²/(c₀²N⁴)`, every
`z ∈ [0, 1]²` with `‖g_π(z)‖ ≤ ϵ` (proximal gradient of `F = Fnorm C` on `[0, 1]²` with smoothness
constant 1) lies in `[1/12, 11/12]²`. -/
theorem frame_kkt_margin (C : Circuit) (hC : C.WF) (hN : 40 ≤ gridN C.n) (z : Fin 2 → ℝ)
    (hz : IsApproxKKT boxA boxB 1 ((epsF (gridN C.n) : ℚ) : ℝ) z (gradVec (Fnorm C) z)) :
    ∀ i, (1 / 12 : ℝ) ≤ z i ∧ z i ≤ 11 / 12 := by sorry

end ConstrSOSP
