-- Prove2me | Theorems.Thm_ConstrSOSP_groupX_localisation
-- name    : ConstrSOSP.groupX_localisation
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:06:48.253941+00:00
-- url     : https://prove2.me/theorems/f6d2dd09-8299-4bf4-a8f9-b59812c3c26e
-- title:
--   Every $(\epsilon_0,\epsilon_0)$-SOSP of $f$ lies in a Group X cell of an Iter solution
-- statement:
--   Let $C$ be an Iter instance (well formed, $C(1)>1$) with $N=6\cdot2^n+6\ge10^{40}$, let $f$ be the constructed function on $[0,N]^2$ and $\epsilon_0=10^{-10}$.
--
--   **Theorem.**
--
--   1. Every global minimizer of $f$ over $[0,N]^2$ lies in the open square $(0,N)^2$.
--   2. Every $z\in(0,N)^2$ with $\|\nabla f(z)\|\le\epsilon_0$ and $\nabla^2f(z)\succeq-\epsilon_0I$ lies in a Group X cell $\mathrm{Box}(6k-r,6k+2)$, $r\in\{1,2,3\}$, of some Iter solution $k$.
--
--   The first part shows that an exact SOSP exists; the second that every approximate SOSP reveals an Iter solution. This is the core of the reduction on the unnormalized grid.
--
--   Differences from the source:
--   - encoding: ∇f, ∇²f of the C² function → Mathlib Fréchet derivatives (gradVec, hessMat); vector norms written out as Euclidean norms; reason: Lean convention; same values for C² functions
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), end of §5.4.3, p.49

import Mathlib
import Definitions.Def_ConstrSOSP_Circuit_WF
import Definitions.Def_ConstrSOSP_Circuit_app
import Definitions.Def_ConstrSOSP_gridN
import Definitions.Def_ConstrSOSP_fGrid
import Definitions.Def_ApproxVI_euclNorm
import Definitions.Def_ConstrSOSP_gradVec
import Definitions.Def_ConstrSOSP_hessMat
import Definitions.Def_ConstrSOSP_eps0
import Definitions.Def_ConstrSOSP_InGroupXCell

namespace ConstrSOSP

/-- **Every approximate SOSP of `f` lies in a Group X cell** (arXiv:2604.02285, 2 Nov 2026, end of
§5.4.3, p.49: "We classify such boxes into the Group X (see Figure 14). Since the domain is
compact, a global minimum exists. The boundary analysis places it in the interior, where it is an
exact SOSP. The group estimates place every (ϵ0, ϵ0)-SOSP, and therefore every (ϵ, ϵ)-SOSP with
0 < ϵ ≤ ϵ0, in a Group X cell. Thus every such point identifies an Iter solution k*.").

Let `C` be an Iter instance (well-formed, `C(1) > 1`) with `N = 6·2ⁿ + 6 ≥ 10⁴⁰`, `f = fGrid C`
and `ϵ₀ = 10⁻¹⁰`. Then
1. every global minimizer of `f` over `[0, N]²` lies in the open square `(0, N)²`;
2. every `z ∈ (0, N)²` with `‖∇f(z)‖ ≤ ϵ₀` and `yᵀ∇²f(z)y ≥ −ϵ₀` for all unit `y` (an
   `(ϵ₀, ϵ₀)`-SOSP, Definition 4.9) lies in a Group X cell `Box(6k − r, 6k + 2)`, `r ∈ {1, 2, 3}`,
   of some Iter solution `k ∈ Solutions`. -/
theorem groupX_localisation (C : Circuit) (hC : C.WF) (h1 : 1 < C.app 1)
    (hN : 10 ^ 40 ≤ gridN C.n) :
    (∀ z : Fin 2 → ℝ, (∀ i, 0 ≤ z i ∧ z i ≤ (gridN C.n : ℝ)) →
      (∀ w : Fin 2 → ℝ, (∀ i, 0 ≤ w i ∧ w i ≤ (gridN C.n : ℝ)) → fGrid C z ≤ fGrid C w) →
      ∀ i, 0 < z i ∧ z i < (gridN C.n : ℝ)) ∧
    ∀ z : Fin 2 → ℝ, (∀ i, 0 < z i ∧ z i < (gridN C.n : ℝ)) →
      ApproxVI.euclNorm (gradVec (fGrid C) z) ≤ (eps0 : ℝ) →
      (∀ y : Fin 2 → ℝ, ApproxVI.euclNorm y = 1 → -(eps0 : ℝ) ≤ y ⬝ᵥ Matrix.mulVec (hessMat (fGrid C) z) y) →
      InGroupXCell C z := by sorry

end ConstrSOSP
