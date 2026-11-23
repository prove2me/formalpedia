-- Prove2me | Theorems.Thm_DriftVarCtrl_FixedLB_Supplement_theorem_3
-- name    : DriftVarCtrl.FixedLB.Supplement.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T10:41:49.419803+00:00
-- url     : https://prove2.me/theorems/10c970ac-873e-405e-af12-f45d30b0d680
-- title:
--   Theorem 3, pp. 19–20 (corrected: h₂ ≥ hᵀ₂ in (a), h₁ ≥ hᵀ₁ in (b)) — abandoning early is optimal iff (21), (22) or (23)
-- statement:
--   Consider the free-lower-boundary problem: the entrepreneur chooses a stopping interval policy, with any stopping level $z_0<U$, and minimizes the expected cost. Let $h^+_i$ be the thresholds (17), $h^T_i$ the interaction thresholds (20), $w=\frac{v_2(\mu_2h_1-h_2\mu_1)}{h_1\mu_2(v_2-v_1)}$ and $\xi_U(h_1,h_2,w)$ the function (24). It is optimal for the entrepreneur to abandon early (some optimal stopping interval policy stops at a level $z_0>0$) if and only if one of the following holds:
--
--   1. (a′) $h_1>h^+_1$ and $h_2\ge h^T_2$;
--   2. (b′) $h_1\ge h^T_1$ and $h_2>h^+_2$;
--   3. (c) $h_1\in(h^+_1,h^T_1)$, $h_2\in(h^+_2,h^T_2)$ and
--   $$\xi_U(h_1,h_2,w)<M .$$
--
--   Theorem 3 gives the region of the cost plane in which the venture is abandoned before the state reaches $0$ (Figure 6): it is bounded by two half-lines and the convex curve $\xi_U=M$ through $(h^+_1,h^T_2)$ and $(h^T_1,h^+_2)$.
--
--   **Formalization Note** Optimality is over every stopping interval policy with the analytic value of the definition `FreeModel`. The standing $v_1<v_2$ of p. 12 is a hypothesis.
--
--   Differences from the source:
--
--   - correction: (a) h₁ > h⁺₁, h₂ > hᵀ₂ and (b) h₁ > hᵀ₁, h₂ > h⁺₂ → (a′) h₁ > h⁺₁, h₂ ≥ hᵀ₂ and (b′) h₁ ≥ hᵀ₁, h₂ > h⁺₂; reason: on the segments h₂ = hᵀ₂, h₁ ∈ (h⁺₁, hᵀ₁] and h₁ = hᵀ₁, h₂ ∈ (h⁺₂, hᵀ₂] no printed condition holds, yet ξ_U < M there (ξ_U decreases in h₁ and h₂ and equals M at (h⁺₁, hᵀ₂) and (hᵀ₁, h⁺₂), Lemma 13 (122)–(124)), so the proof's own argument gives Ũ < U; at μ = (1, 2), σ = (1, 1), M = −20, U = 10 and (h₁, h₂) = (hᵀ₁, hᵀ₂) ≈ (4.103, 4.211) or (hᵀ₁, 4.15) a brute force over stopping policies finds the optimal stopping level above 0 while no printed condition holds; only these boundary segments change
--   - reading: hᵀ₁ = (1/dᴸ₂)Δh₂ + h*₁ and hᵀ₂ = dᵁ₁Δh₁ + h*₂ (20) → hᵀ₁ = (1/dᴸ₂)(h⁺₂ − h*₂) + h*₁ and hᵀ₂ = dᵁ₁(h⁺₁ − h*₁) + h*₂; reason: Figure 5 draws hᵀᵢ as a fixed threshold on the hᵢ axis, and Figure 6, Lemma 13 (123)–(124), Lemma 16 and the proof of Theorem 3 use the points (h⁺₁, hᵀ₂) and (hᵀ₁, h⁺₂)
--   - encoding: it is optimal to abandon early; the expected cost (112) → AbandonsEarly p: some IsStopOptimal stopping interval policy has z₀ > 0, with the analytic value IsStopValue; reason: the proof (p. EC-27) reads abandoning early as an optimal stopping level above 0; Mathlib has no stochastic integral, and the analytic value is the system (115) the paper writes
-- source:
--   Wang, Zenios, New Venture Creation: A Drift-Variance Diffusion Control Model, SSRN 3667132 (working paper, sha256 2d7a57ba…), pp. 19–20, Theorem 3, (21)–(24) (proof pp. EC-27–EC-28)

import Mathlib
import Definitions.Def_DriftVarCtrl_FixedLB_Model
import Definitions.Def_DriftVarCtrl_FixedLB_Supplement_FreeModel
import Definitions.Def_DriftVarCtrl_FixedLB_Supplement_Thresholds

namespace DriftVarCtrl.FixedLB.Supplement

open DriftVarCtrl.FixedLB

/-- Theorem 3, corrected on two boundary segments (Wang, Zenios, New Venture Creation: A Drift-Variance Diffusion Control Model, SSRN 3667132 (working paper, sha256 2d7a57ba…), pp. 19–20, (21)–(24); proof
pp. EC-27–EC-28). With a free lower boundary, it is optimal for the entrepreneur to abandon early
(some optimal stopping interval policy stops at a level `z₀ > 0`) if and only if
(a′) `h₁ > h⁺₁` and `h₂ ≥ hᵀ₂`, or (b′) `h₁ ≥ hᵀ₁` and `h₂ > h⁺₂`, or
(c) `h₁ ∈ (h⁺₁, hᵀ₁)`, `h₂ ∈ (h⁺₂, hᵀ₂)` and `ξ_U(h₁, h₂, w) < M`.

Formalization Note: the page prints (a) with `h₂ > hᵀ₂` and (b) with `h₁ > hᵀ₁`. On the segments
`h₂ = hᵀ₂`, `h₁ ∈ (h⁺₁, hᵀ₁]` and `h₁ = hᵀ₁`, `h₂ ∈ (h⁺₂, hᵀ₂]` none of the printed conditions
holds, yet `ξ_U < M` there (ξ_U decreases in `h₁, h₂` and equals `M` at `(h⁺₁, hᵀ₂)` and
`(hᵀ₁, h⁺₂)`, Lemma 13), so the optimal stopping level is above `0`; at `μ = (1, 2)`,
`σ = (1, 1)`, `M = −20`, `U = 10`, `(h₁, h₂) = (hᵀ₁, hᵀ₂)` a brute force over stopping policies
gives an optimal stopping level above `0`. The weak inequalities repair this. `hᵀᵢ` is (20) read at
the other control's `h⁺` (`hT1`, `hT2`). Policy values are the analytic `IsStopValue`; the
standing `v₁ < v₂` (p. 12) is `hv`. -/
theorem theorem_3 (p : Params) (hv : v p .one < v p .two) :
    AbandonsEarly p ↔
      (hplus p .one < p.h₁ ∧ hT2 p ≤ p.h₂) ∨
      (hT1 p ≤ p.h₁ ∧ hplus p .two < p.h₂) ∨
      (p.h₁ ∈ Set.Ioo (hplus p .one) (hT1 p) ∧ p.h₂ ∈ Set.Ioo (hplus p .two) (hT2 p) ∧
        xi p p.U p.h₁ p.h₂ (wFB p p.h₁ p.h₂) < p.M) := by sorry

end DriftVarCtrl.FixedLB.Supplement
