-- Prove2me | Theorems.Thm_CorrWardrop_kkt_iff_saddle
-- name    : CorrWardrop.kkt_iff_saddle
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:29:14.534583+00:00
-- url     : https://prove2.me/theorems/f2b00daf-53e2-4e53-a673-fbd709487ef0
-- title:
--   Proof of Proposition 4, p.19 — KKT conditions iff saddle point of the Lagrangian (corrected: Lagrangian includes the −γ^k term)
-- statement:
--   Let $\Gamma$ be a nonatomic game and let $\Phi$ be a convex potential of $\Gamma$ on the open convex set $U\supseteq\mathcal Y$ (so $\Phi$ is continuously differentiable and convex on $U$, and $\partial\Phi/\partial y^k_a=c^k_a$ on $\mathcal Y$). Let
--   $$
--   \mathcal L(y,\lambda)=\Phi(y)-\sum_{k}\lambda^k\Big(\sum_{a\in\mathcal A^k}y^k_a-\gamma^k\Big)-\sum_k\sum_{a\in\mathcal A^k}\lambda^k_a\,y^k_a .
--   $$
--   For $\hat y\in\mathcal Y$ and multipliers $\hat\lambda$, the pair $(\hat y,\hat\lambda)$ satisfies the KKT conditions if and only if it is a saddle point of $\mathcal L$: $\hat\lambda^k_a\ge 0$ for all $k,a$, and
--   $$
--   \mathcal L(\hat y,\lambda)\le\mathcal L(\hat y,\hat\lambda)\le\mathcal L(y,\hat\lambda)
--   $$
--   for every $y\in U$ and every $\lambda$ with $\lambda^k_a\ge 0$ for all $k,a$.
--
--   The saddle-point form is what makes the exchange property available: optimal primal solutions and optimal multipliers can be recombined freely.
--
--   Differences from the source:
--   - correction: L(y, λ) = Φ(y) − Σ_k λ^k (Σ_a y^k_a) − Σ_k Σ_a λ_{a,k} y^k_a → L(y, λ) = Φ(y) − Σ_k λ^k (Σ_a y^k_a − γ^k) − Σ_k Σ_a λ^k_a y^k_a; reason: with the printed L no saddle point exists, so "KKT iff saddle" is false: one population, one action, γ = 1, c ≡ 0, Φ ≡ 0; ŷ = 1 with λ̂ = 0 satisfies KKT but L(ŷ, λ) = −λ^1 has no maximum in λ^1
--   - reading: for all (y, λ) → for all y ∈ U (the open convex domain on which Φ is a convex potential) and all λ with λ^k_a ≥ 0 (λ^k free); also λ̂^k_a ≥ 0; reason: the domain of the Lagrangian in Rockafellar's Theorem 28.3, which the page cites
-- source:
--   Koessler–Scarsini–Tomala, Correlated Equilibria in Large Anonymous Bayesian Games, arXiv:2107.06312v4, proof of Proposition 4, saddle-point display, p.19 (citing Rockafellar 1970, Theorem 28.3)

import Mathlib
import Definitions.Def_CorrWardrop_Model
import Definitions.Def_CorrWardrop_Lagrangian
open MeasureTheory

namespace CorrWardrop

/-- Proof of Proposition 4, KKT conditions and saddle points (corrected Lagrangian): let `Φ` be
a convex potential of `Γ` on the open convex neighbourhood `U` of `Y`. For `ŷ ∈ Y` and
multipliers `λ̂`, `(ŷ, λ̂)` satisfies the KKT conditions if and only if
`L(ŷ, λ) ≤ L(ŷ, λ̂) ≤ L(y, λ̂)` for all `y ∈ U` and all `λ` with `λ^k_a ≥ 0` (and `λ̂^k_a ≥ 0`).

Koessler–Scarsini–Tomala, arXiv:2107.06312v4, proof of Proposition 4, p.19 (Rockafellar 1970,
Theorem 28.3).

Formalization Note: `L` is the corrected Lagrangian `lagrangian`, which contains the `−γ^k` of
the equality constraints; with the printed `L` there is no saddle point. -/
theorem kkt_iff_saddle {K : Type*} [Fintype K] {A : K → Type*} [∀ k, Fintype (A k)]
    [DecidableEq K] [∀ k, DecidableEq (A k)]
    (Γ : NonatomicGame K A) (Φ : Flow A → ℝ) (U : Set (Flow A))
    (hΦ : IsConvexPotentialOn Γ Φ U) (y : Γ.Y) (l : Multipliers A) :
    KKT Γ Φ y l ↔ IsSaddle Γ Φ U y l := by sorry

end CorrWardrop
