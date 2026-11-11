-- Prove2me | Theorems.Thm_ExpanderWalkDecode_Main_claim5_reflection_hoeffding
-- name    : ExpanderWalkDecode.Main.claim5_reflection_hoeffding
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:21:37.700133+00:00
-- url     : https://prove2.me/theorems/6693c13d-4942-43ac-8296-cea444a34f11
-- title:
--   Claim 5 — Hoeffding bound for signed reflections across low-rank subspaces
-- statement:
--   There is an absolute constant $C>0$ with the following property. Let $R\ge2$, let $\{T_v\}_{v\in V}$ be real symmetric $D\times D$ matrices (indexed by a finite set $V$) such that $\Pi_v=\tfrac12(I+T_v)$ is the orthogonal projection onto a subspace of dimension at most $R$, let $\sigma\in\{\pm1\}^V$, and $M=\mathbb E_{v\sim V}[\sigma_vT_v]$. For all $\eta,\delta>0$, if $\ell\ge\frac{C}{\eta^2}\log\frac R\delta$, then for independent uniform $v_1,\dots,v_\ell\in V$ and $\widehat M=\mathbb E_{i\sim[\ell]}[\sigma_{v_i}T_{v_i}]$,
--   $$\Pr\big[\|\widehat M-M\|_{\mathrm{op}}>\eta\big]\le\delta .$$
--   The constant does not depend on $D$, $R$, $V$, the signs, $\eta$ or $\delta$.
--
--   The sample size depends on the rank bound $R$, not on the dimension $D$; this is what makes the guessing step of the rounding algorithm affordable.
--
--   Differences from the source:
--   - encoding: T_v a reflection across a subspace H_v of dimension ≤ R → (I+T_v)/2 symmetric, idempotent, of rank ≤ R; reason: equivalent description of an orthogonal projection onto a subspace of dimension ≤ R
-- source:
--   Silas Richelson, Sourya Roy, Madhur Tulsiani, Decoding Expander Walk Codes up to the Johnson Bound in Near-Linear Time, STOC 2027 submission #1736 (October 2026), p. 9 (PDF p. 12), §3.2, Claim 5

import Mathlib
import Definitions.Def_ExpanderWalkDecode_Main_Graphs

namespace ExpanderWalkDecode.Main

open scoped Matrix

/-- Claim 5 (§3.2, p. 9): there is an absolute constant `C > 0` such that, for real symmetric
`D × D` matrices `T_v` that are reflections across subspaces of dimension at most `R ≥ 2`
(`(I + T_v)/2` is the orthogonal projection onto the subspace), signs `σ_v ∈ {±1}`,
`M = E_v[σ_v T_v]`, and all `η, δ > 0`: if `ℓ ≥ (C/η²) log(R/δ)`, then `ℓ` i.i.d. uniform samples
give `Pr[‖M̂ - M‖_op > η] ≤ δ` for `M̂ = E_{i∼[ℓ]}[σ_{v_i} T_{v_i}]`. -/
theorem claim5_reflection_hoeffding :
    ∃ C : ℝ, 0 < C ∧ ∀ (D R : ℕ) (V : Type) [Fintype V] [Nonempty V]
      (T : V → Matrix (Fin D) (Fin D) ℝ) (σ : V → ℝ),
      2 ≤ R → (∀ v, (T v)ᵀ = T v) →
      (∀ v, ((1 / 2 : ℝ) • (1 + T v))ᵀ = (1 / 2 : ℝ) • (1 + T v) ∧
        (1 / 2 : ℝ) • (1 + T v) * ((1 / 2 : ℝ) • (1 + T v)) = (1 / 2 : ℝ) • (1 + T v) ∧
        ((1 / 2 : ℝ) • (1 + T v)).rank ≤ R) →
      (∀ v, σ v = 1 ∨ σ v = -1) →
      ∀ η δ : ℝ, 0 < η → 0 < δ → ∀ ℓ : ℕ, C / η ^ 2 * Real.log (R / δ) ≤ ℓ →
        sampleProb ℓ (fun v : Fin ℓ → V =>
          η < opNorm ((avg fun i => σ (v i) • T (v i)) - avg fun w => σ w • T w)) ≤ δ := by sorry

end ExpanderWalkDecode.Main
