-- Prove2me | Theorems.Thm_AlgoPFR_claim_4_12_good_iteration
-- name    : AlgoPFR.claim_4_12_good_iteration
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:45:13.915195+00:00
-- url     : https://prove2.me/theorems/ae86fb9b-d97e-4324-81c1-2761b3d8a33a
-- title:
--   Claim 4.12 — one iteration is good with probability $\ge\eta/40$
-- statement:
--   Let $\eta\in(0,1)$ have the property promised by Theorem 4.3, and let $L_0=256/\eta$, $\xi=768/\eta$, $d_{\mathrm{term}}=\max\{L_0+1,\frac{16}\eta\log\frac{64}\eta\}$. Suppose we have algorithmic access to $X_{t-1},Y_{t-1}$ with $\Delta[X_{t-1}],\Delta[Y_{t-1}]\le L_0$, and let $d=\max\{d[X_{t-1};Y_{t-1}],d_{\mathrm{term}}\}$. Then one iteration of Algorithm 2 outputs $X_t,Y_t$ such that, with probability at least $\eta/40$,
--   $$\Phi_{X_{t-1},Y_{t-1}}(X_t,Y_t)\le(1-\eta/2)d,\quad\Delta[X_t],\Delta[Y_t]\le L_0,\quad C_{\mathrm{access}}\le\xi(d+1).$$
--
--   This is the step that replaces the non-constructive choice of a family in the GGMT argument by a uniformly random one.
--
--   Differences from the source:
--
--   - reading: "steps 6–4.4.1 of Algorithm 2" → lines 6–8 of Algorithm 2; reason: a broken cross-reference: 4.4.1 is a subsection number, and lines 6–8 are the steps of an iteration
--   - generalization: η the constant fixed after Theorem 4.3 → every η ∈ (0, 1) with IsDecrementConstant η; reason: the fixed constant is one such η, once taken below 1; the proof uses only this property
-- source:
--   Arunachalam, Dutt, Grewal, Gupte, Marton's conjecture in polynomial time, arXiv:2609.20771 (sha256 60e45066…), Claim 4.12, p.33

import Mathlib
import Definitions.Def_AlgoPFR_Iteration

set_option autoImplicit false

open scoped ENNReal Pointwise

namespace AlgoPFR

/-- **Claim 4.12.** Arunachalam, Dutt, Grewal, Gupte, *Marton's conjecture in polynomial time*, arXiv:2609.20771 (sha256 60e45066…), p.33: let `η ∈ (0, 1)` be the promise of Theorem 4.3, `L₀ = 256/η`, `ξ = 768/η`,
`d_term = max {L₀ + 1, (16/η) log (64/η)}`. If `Δ[X_{t−1}], Δ[Y_{t−1}] ≤ L₀` and
`d := max {d[X_{t−1};Y_{t−1}], d_term}`, then one iteration of Algorithm 2 outputs `X_t, Y_t` with
probability `≥ η/40` such that `Φ_{X_{t−1},Y_{t−1}}(X_t, Y_t) ≤ (1 − η/2) d`, `Δ[X_t], Δ[Y_t] ≤ L₀` and
`C_access ≤ ξ (d + 1)`.

**Formalization Note.** The printed "steps 6–4.4.1" is a broken reference; it means lines 6–8 of
Algorithm 2. The claim is stated for every `η ∈ (0, 1)` with the property of Theorem 4.3, not for one
chosen `η`. All the outcomes form a countable-support law, so `toOuterMeasure` is its probability. -/
theorem claim_4_12_good_iteration {n : ℕ} (η : ℝ) (h0 : 0 < η) (h1 : η < 1)
    (hη : IsDecrementConstant η) (s : AccessState n) (hX : IsAccess s.X s.MX)
    (hY : IsAccess s.Y s.MY) (hΔX : slack s.X s.MX ≤ L0 η) (hΔY : slack s.Y s.MY ≤ L0 η) :
    ENNReal.ofReal (η / 40) ≤ (iterationLaw s).toOuterMeasure {e | IsGoodIteration η s e} := by sorry

end AlgoPFR
