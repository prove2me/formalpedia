-- Prove2me | Theorems.Thm_FairFlows_claim_3_3
-- name    : FairFlows.claim_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:16:46.948803+00:00
-- url     : https://prove2.me/theorems/5d7f7990-c8bc-4052-9852-bf5f5fc4f6fc
-- title:
--   Claim 3.3 — the optimal $y^*$ may be chosen $(0,1)$-valued
-- statement:
--   Let $D_L=(V,L)$ cover the intersecting supermodular function $p$. Then the dual program (3.3), $\max\{yp-\mathbf 1z: yA_L-z\le\mathbf 1,\ (y,z)\ge0\}$, has an integer-valued optimal solution $(y^*,z^*)$ whose support family $\{Z:y^*(Z)>0\}$ is laminar and with $y^*(Z)\in\{0,1\}$ for every row $Z$.
--
--   The claim turns the laminar dual optimum of Theorem 3.1 into a laminar family of sets, each used once, which is what the formula (3.4) counts.
--
--   Differences from the source:
--   - generalization: a digraph D = (V, A) (parallel edges are used; loops are not discussed) → edges are a finite type with tail/head maps, so parallel edges and loops are allowed; reason: a loop enters and leaves no set and cancels in ϱ_x(v) − δ_x(v); loop-free digraphs are the special case
--   - encoding: a digraph D_L = (V, L) → an edge subset L of a digraph D (D_L is D with L = all edges); reason: Lean convention; same instances
--   - reading: "The optimal y* may be chosen (0, 1)-valued", referring to the integer-valued dual optimum with laminar support chosen in the proof → there is an integer-valued optimal solution of (3.3) with laminar support and y* ∈ {0,1}; reason: the claim's y* is that optimum; the statement makes the reference explicit
-- source:
--   Frank, Murota, Fair integral network flows, arXiv:1907.02673v5, Claim 3.3, p.8 (in the proof of Theorem 3.2)

import Mathlib
import Definitions.Def_FairFlows_CoverLP

set_option autoImplicit false

namespace FairFlows

/-- Claim 3.3 (Frank, Murota, *Fair integral network flows*, arXiv:1907.02673v5, p.8, in the proof of Theorem 3.2): "The optimal `y*` may be chosen
`(0, 1)`-valued." Under the hypotheses of Theorem 3.1 (`D_L` covers the intersecting
supermodular `p`), the dual program (3.3) has an integer-valued optimal solution `(y*, z*)` whose
support family is laminar and with `y*` taking only the values `0` and `1`.

**Formalization Note** The optimum `(y*, z*)` the claim refers to is the integer-valued dual
optimum with laminar support of Theorem 3.1, chosen in the proof of Theorem 3.2; the claim is
stated as the existence of such an optimum that is moreover `(0,1)`-valued in `y`. -/
theorem claim_3_3 {V A : Type} [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A]
    (D : Digraph V A) (L : Finset A) (p : Finset V → WithBot ℤ)
    (hp : IsIntersectingSupermodular p) (hcov : Covers D L p) :
    ∃ y z, IsCoverDualOpt D L p (fun _ => 1) y z ∧ IsIntegral y ∧ IsIntegral z ∧
      IsLaminar (dualSupport y) ∧ ∀ X, y X = 0 ∨ y X = 1 := by sorry

end FairFlows
