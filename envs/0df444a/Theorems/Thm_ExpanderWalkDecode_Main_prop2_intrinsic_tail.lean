-- Prove2me | Theorems.Thm_ExpanderWalkDecode_Main_prop2_intrinsic_tail
-- name    : ExpanderWalkDecode.Main.prop2_intrinsic_tail
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:21:27.044424+00:00
-- url     : https://prove2.me/theorems/66abe0ef-5651-4c9f-876d-66aa2aea823c
-- title:
--   Proposition 2 — intrinsic-dimension matrix tail bound for i.i.d. samples
-- statement:
--   Let $\beta,\sigma,\kappa>0$ and let $\{X_v\}_{v\in V}$ be real symmetric matrices indexed by a finite set $V$ with
--
--   1. $\mathbb E_{v\sim V}[X_v]=0$;
--   2. $\|X_v\|_{\mathrm{op}}\le\beta$ for all $v$;
--   3. $\|\mathbb E_{v\sim V}[X_v^2]\|_{\mathrm{op}}\le\sigma^2$;
--   4. $\operatorname{tr}\mathbb E_{v\sim V}[X_v^2]\le\sigma^2\kappa$.
--
--   Then for every sample size $\ell\ge1$ and every $t>0$, for independent uniform $v_1,\dots,v_\ell\in V$,
--   $$\Pr\Big[\big\|\mathbb E_{i\sim[\ell]}X_{v_i}\big\|_{\mathrm{op}}>\sqrt{\tfrac{2\sigma^2t}{\ell}}+\tfrac{\beta t}{3\ell}\Big]\le\frac{2\kappa t}{e^t-t-1}.$$
--
--   The bound depends on the intrinsic dimension $\kappa$ instead of the ambient dimension; Claim 5 is deduced from it.
--
--   Differences from the source:
--   - encoding: any ℓ ∈ ℕ → ℓ ≥ 1; reason: the empirical average over [0] is undefined
-- source:
--   Silas Richelson, Sourya Roy, Madhur Tulsiani, Decoding Expander Walk Codes up to the Johnson Bound in Near-Linear Time, STOC 2027 submission #1736 (October 2026), p. 9 (PDF p. 12), §3.2, Proposition 2

import Mathlib
import Definitions.Def_ExpanderWalkDecode_Main_Graphs

namespace ExpanderWalkDecode.Main

open scoped Matrix

/-- Proposition 2 (specialization of Theorem 4 of [HKZ12]) (§3.2, p. 9): for real symmetric
`X_v` (`v ∈ V`) with `E_v X_v = 0`, `‖X_v‖_op ≤ β`, `‖E_v X_v²‖_op ≤ σ²` and
`tr E_v X_v² ≤ σ² κ`, and for `ℓ` i.i.d. uniform samples and every `t > 0`,
`Pr[‖E_{i∼[ℓ]} X_{v_i}‖_op > √(2σ²t/ℓ) + βt/(3ℓ)] ≤ 2κt/(e^t - t - 1)`. -/
theorem prop2_intrinsic_tail {V : Type} [Fintype V] [Nonempty V] {D : ℕ}
    (X : V → Matrix (Fin D) (Fin D) ℝ) (β σ κ : ℝ) (hβ : 0 < β) (hσ : 0 < σ) (hκ : 0 < κ)
    (hsymm : ∀ v, (X v)ᵀ = X v) (h1 : avg X = 0) (h2 : ∀ v, opNorm (X v) ≤ β)
    (h3 : opNorm (avg fun v => X v * X v) ≤ σ ^ 2)
    (h4 : (avg fun v => X v * X v).trace ≤ σ ^ 2 * κ) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (t : ℝ) (ht : 0 < t) :
    sampleProb ℓ (fun v : Fin ℓ → V =>
        Real.sqrt (2 * σ ^ 2 * t / ℓ) + β * t / (3 * ℓ) < opNorm (avg fun i => X (v i)))
      ≤ 2 * κ * t / (Real.exp t - t - 1) := by sorry

end ExpanderWalkDecode.Main
