-- Prove2me | Theorems.Thm_CubeSampling_proposition_3_4
-- name    : CubeSampling.proposition_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:17:14.637382+00:00
-- url     : https://prove2.me/theorems/16eb6715-c2a3-4db7-9ad4-b4278510dddd
-- title:
--   Proposition 3.4 — clipping gives stable sampling
-- statement:
--   **Proposition 3.4.** Let $V$ have dimension $m$, with orthonormal basis $\Phi_V$. Suppose $\mathbb E[h^2 \wedge B] \ge \alpha$ for every unit $h \in V$, where $B \ge 1$ and $0 < c < \alpha < 1$. Then there is $C_{\alpha,c}$, depending only on $\alpha$ and $c$, such that for $X_1,\dots,X_n$ i.i.d. $\mu_d$,
--   $$
--   n \ge C_{\alpha,c}\, B\,(m + t) \implies P\bigl(\hat\Sigma_V \succeq c I_m\bigr) \ge 1 - e^{-t}.
--   $$
--
--   Unit elements of $V$ are $h = \sum_j a_j\varphi_j$ with $\sum_j a_j^2 = 1$. Together with Proposition 3.3 this gives stable sampling at $n \ge C(m+t)e^{\Lambda_{d,k} + Ck^{1/3}}$.
--
--   Differences from the source:
--   - encoding: an m-dimensional subspace V with its orthonormal basis Φ_V → an orthonormal family Φ : Fin m → (cube → ℝ); reason: the paper notes the choice of basis is arbitrary; V = span Φ
--   - generalization: V ⊆ P_{d,k} (the standing setup of §1.1) → V the span of any orthonormal family of functions on the cube; reason: the statement and its proof use only orthonormality; it specializes to V ⊆ P_{d,k}
-- source:
--   Weinberger, Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube, arXiv:2610.12358 (version of 2 Nov 2026), Proposition 3.4, p.14

import Mathlib
import Definitions.Def_CubeSampling_IsOrthonormalFamily
import Definitions.Def_CubeSampling_cubeMeasure
import Definitions.Def_CubeSampling_empCov
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace CubeSampling

/-- Proposition 3.4 (clipping gives stable sampling) (Weinberger, *Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube*, arXiv:2610.12358 (version of 2 Nov 2026, sha256 43fdcd90…4f79), Proposition 3.4, p.14): let `V` have
dimension `m` (orthonormal basis `Φ`) and suppose `E[h² ∧ B] ≥ α` for every unit `h ∈ V`, where `B ≥ 1`
and `0 < c < α < 1`. Then `n ≥ C_{α,c} B (m + t)` implies `P(Σ̂_V ⪰ c I_m) ≥ 1 − e^{−t}`.

**Formalization Note** Unit `h ∈ V` are `h = ∑_j a_j φ_j` with `∑_j a_j² = 1`; `t` is any real number; `V` is
any `m`-dimensional space of functions on the cube. -/
theorem proposition_3_4 (α c : ℝ) (hc : 0 < c) (hcα : c < α) (hα : α < 1) :
    ∃ C : ℝ, ∀ (d m : ℕ) (Φ : Fin m → Cube d → ℝ), IsOrthonormalFamily Φ →
      ∀ B : ℝ, 1 ≤ B →
      (∀ a : Fin m → ℝ, ∑ j, a j ^ 2 = 1 →
        α ≤ cubeMean d (fun x => min ((∑ j, a j * Φ j x) ^ 2) B)) →
      ∀ t : ℝ, ∀ n : ℕ, C * B * (m + t) ≤ n →
        ENNReal.ofReal (1 - Real.exp (-t)) ≤
          (Measure.pi fun _ : Fin n => cubeMeasure d)
            {X | (empCov Φ n X - c • (1 : Matrix (Fin m) (Fin m) ℝ)).PosSemidef} := by sorry

end CubeSampling
