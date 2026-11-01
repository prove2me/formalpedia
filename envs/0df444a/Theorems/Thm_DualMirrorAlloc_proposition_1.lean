-- Prove2me | Theorems.Thm_DualMirrorAlloc_proposition_1
-- name    : DualMirrorAlloc.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:03:22.424568+00:00
-- url     : https://prove2.me/theorems/380a57c3-88d5-4668-b483-5d144b9e2644
-- title:
--   Proposition 1, p.10 — weak duality $\mathrm{OPT}(\vec\gamma)\le D(\mu|\vec\gamma)$
-- statement:
--   Assume the model of §2 (p.8): $X_s\subseteq\mathbb R^d_+$ compact, $0\in X_s$, $b_s(0)=0$, $f_s,b_s\ge0$ on $X_s$, $\rho>0$. For every horizon $T$, every request sequence $\vec\gamma=(\gamma_1,\dots,\gamma_T)$ and every $\mu\in\mathbb R^m_+$ for which each $f^*_t(\mu)$ is finite,
--   $$
--   \mathrm{OPT}(\vec\gamma)\le D(\mu|\vec\gamma)=\sum_{t=1}^T f^*_t(\mu)+T\rho^\top\mu .
--   $$
--
--   The Lagrangian dual function upper-bounds the offline optimum. Step 3 of the proof of Theorem 1 uses it in expectation.
--
--   **Formalization Note** Finiteness of $f^*_t(\mu)$ is the hypothesis that $\{f_t(x)-\mu^\top b_t(x):x\in X_t\}$ is bounded above; if some $f^*_t(\mu)=+\infty$ the claim is trivial, but Lean's `sSup` of an unbounded set is $0$.
--
--   Differences from the source:
--   - encoding: requests γ = (f, b, X) ∈ S → a type S of requests carrying X s, f s, b s (structure Requests); f s, b s typed on all of ℝ^d; reason: values of f, b off X_s are never used
--   - encoding: OPT(γ⃗) = max (1); f*(µ) = sup (2) → real sSup; reason: under the model and Assumption 1 the sets are nonempty and bounded above, so sSup is the supremum (and the maximum when attained)
--   - encoding: D(µ|γ⃗) may be +∞ → each set {f_t(x) − µᵀb_t(x) : x ∈ X_t} is bounded above; reason: excludes only D = +∞, where the claim holds trivially and Lean's sSup would be 0
--   - generalization: a horizon of T periods (T ≥ 1) → every T : ℕ, including T = 0; reason: the T = 0 case (OPT = D = 0) is added; every T ≥ 1 is an instance
--   - encoding: periods t = 1, …, T → Fin T, 0-based; reason: index convention only
-- source:
--   Balseiro–Lu–Mirrokni, The Best of Many Worlds: Dual Mirror Descent for Online Allocation Problems, arXiv:2011.10124v3, Proposition 1, p.10 (proof Appendix A.1, p.41)

import Mathlib
import Definitions.Def_DualMirrorAlloc_Model

namespace DualMirrorAlloc

/-- **Proposition 1 (weak duality).** Balseiro–Lu–Mirrokni, arXiv:2011.10124v3, Proposition 1, p.10
(proof in Appendix A.1, p.41): "It holds for every µ ∈ Rm+ that OPT(γ⃗) ≤ D(µ|γ⃗)."

For every horizon `T`, every request sequence `γ⃗ ∈ S^T` and every `µ ∈ ℝ^m_+`,
`OPT(γ⃗) ≤ Σ_t f*_t(µ) + Tρᵀµ`.

**Formalization Note.** Under the model of p.8 (`IsModel`). The hypothesis that
`{f_t(x) − µᵀb_t(x) : x ∈ X_t}` is bounded above for every `t` says that `D(µ|γ⃗)` is finite; when
it is `+∞` the claim is trivial, but Lean's `sSup` of an unbounded set is `0`. -/
theorem proposition_1 {S : Type*} {d m : ℕ}
    (R : Requests S d m) (ρ : Fin m → ℝ) (hmodel : IsModel R ρ)
    (T : ℕ) (γ : Fin T → S) (mu : Fin m → ℝ) (hmu : mu ∈ orthant m)
    (hbdd : ∀ t, BddAbove ((fun x => R.f (γ t) x - mu ⬝ᵥ R.b (γ t) x) '' R.X (γ t))) :
    OPT R ρ γ ≤ dualFn R ρ mu γ := by sorry

end DualMirrorAlloc
