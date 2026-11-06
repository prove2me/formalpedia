-- Prove2me | Theorems.Thm_ConstrSOSP_frame_sosp_groupX
-- name    : ConstrSOSP.frame_sosp_groupX
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:08:47.059401+00:00
-- url     : https://prove2.me/theorems/c47331e6-415c-4c32-9e5c-12768e3b6b16
-- title:
--   Every $(\epsilon,\sqrt\epsilon)$-SOSP of $F$ yields an Iter solution
-- statement:
--   Let $C$ be an Iter instance (well formed, $C(1)>1$) with $N=6\cdot2^n+6\ge10^{40}$, $F$ the normalized function, $\epsilon=\epsilon_0^2/(c_0^2N^4)$ and $\sqrt\epsilon=\epsilon_0/(c_0N^2)$.
--
--   **Theorem.** Every $(\epsilon,\sqrt\epsilon)$-SOSP $z$ of $F$ on $[0,1]^2$ (Definition 4.9)
--
--   1. lies in $[1/12,11/12]^2$, and
--   2. is mapped by $u=Sz-m(1,1)$ into a Group X cell of some Iter solution $k$.
--
--   So an approximate SOSP of the final instance reveals an Iter solution, read off from the cell containing $u$.
--
--   Differences from the source:
--   - encoding: ∇f, ∇²f of the C² function → Mathlib Fréchet derivatives (gradVec, hessMat); vector norms written out as Euclidean norms; reason: Lean convention; same values for C² functions
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), proof of Corollary 5.6, pp.56–57; Corollary 5.6, p.55 ("In particular …")

import Mathlib
import Definitions.Def_ConstrSOSP_Circuit_WF
import Definitions.Def_ConstrSOSP_Circuit_app
import Definitions.Def_ConstrSOSP_gridN
import Definitions.Def_ConstrSOSP_frameM
import Definitions.Def_ConstrSOSP_frameS
import Definitions.Def_ConstrSOSP_Fnorm
import Definitions.Def_ConstrSOSP_epsF
import Definitions.Def_ConstrSOSP_sqrtEpsF
import Definitions.Def_ConstrSOSP_boxA
import Definitions.Def_ConstrSOSP_boxB
import Definitions.Def_ConstrSOSP_IsSOSP
import Definitions.Def_ConstrSOSP_gradVec
import Definitions.Def_ConstrSOSP_hessMat
import Definitions.Def_ConstrSOSP_InGroupXCell

namespace ConstrSOSP

/-- **Every (ϵ, √ϵ)-SOSP of `F` yields an Iter solution** (arXiv:2604.02285, 2 Nov 2026, proof of
Corollary 5.6, pp.56–57: "If it also satisfies the second-order condition, the affine change of
variables gives ‖∇f(u)‖ ≤ (c0N⁴/S)ϵ = ϵ0²/(c0S) ≤ ϵ0, and λ_min(∇²f(u)) ≥ −(c0N⁴/S²)√ϵ =
−ϵ0N²/S² ≥ −ϵ0. Every (ϵ, √ϵ)-SOSP is also an ϵ-approximate KKT point by nonexpansiveness of
projection. Thus every such SOSP of F yields an Iter solution"; Corollary 5.6, p.55: "In particular,
every exact KKT point and every (ϵ, √ϵ)-SOSP lies at distance at least 1/12 from the boundary").

For an Iter instance `C` (well-formed, `C(1) > 1`) with `N = 6·2ⁿ + 6 ≥ 10⁴⁰`,
`ϵ = ϵ₀²/(c₀²N⁴)` and `√ϵ = ϵ₀/(c₀N²)`: every `(ϵ, √ϵ)`-SOSP `z` of `F = Fnorm C` on `[0, 1]²`
(Definition 4.9) lies in `[1/12, 11/12]²`, and the point `u = Sz − m(1, 1)` lies in a Group X cell
of some Iter solution `k ∈ Solutions`. -/
theorem frame_sosp_groupX (C : Circuit) (hC : C.WF) (h1 : 1 < C.app 1)
    (hN : 10 ^ 40 ≤ gridN C.n) (z : Fin 2 → ℝ)
    (hz : IsSOSP boxA boxB ((epsF (gridN C.n) : ℚ) : ℝ) ((sqrtEpsF (gridN C.n) : ℚ) : ℝ) z
      (gradVec (Fnorm C) z) (hessMat (Fnorm C) z)) :
    (∀ i, (1 / 12 : ℝ) ≤ z i ∧ z i ≤ 11 / 12) ∧
      InGroupXCell C (fun i => (frameS C.n : ℝ) * z i - (frameM C.n : ℝ)) := by sorry

end ConstrSOSP
