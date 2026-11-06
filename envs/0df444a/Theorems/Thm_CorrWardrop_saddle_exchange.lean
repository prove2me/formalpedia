-- Prove2me | Theorems.Thm_CorrWardrop_saddle_exchange
-- name    : CorrWardrop.saddle_exchange
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T11:29:18.616421+00:00
-- url     : https://prove2.me/theorems/6c9008f4-ef6e-4fb5-8357-07d97c704372
-- title:
--   Proof of Proposition 4, p.19 — exchange property of saddle points of the Lagrangian (corrected: Lagrangian includes the −γ^k term)
-- statement:
--   Let $\Gamma$ be a nonatomic game, $\Phi$ a real function on the flow space, $U$ a set of flow vectors, and $\mathcal L$ the Lagrangian
--   $$
--   \mathcal L(y,\lambda)=\Phi(y)-\sum_{k}\lambda^k\Big(\sum_{a\in\mathcal A^k}y^k_a-\gamma^k\Big)-\sum_k\sum_{a\in\mathcal A^k}\lambda^k_a\,y^k_a .
--   $$
--   If $(\hat y,\hat\lambda)$ and $(\bar y,\bar\lambda)$ are saddle points of $\mathcal L$ on $U\times\{\lambda:\lambda^k_a\ge0\ \forall k,a\}$, then $(\hat y,\bar\lambda)$ and $(\bar y,\hat\lambda)$ are also saddle points.
--
--   In the proof of Proposition 4 this is applied to two Wardrop equilibria: the multipliers of one serve for the other, so the partial derivatives $\partial\Phi/\partial y^k_a$, i.e. the costs, coincide wherever the multipliers determine them.
--
--   Differences from the source:
--   - correction: saddle points of the printed L(y, λ) = Φ(y) − Σ_k λ^k (Σ_a y^k_a) − Σ_k Σ_a λ_{a,k} y^k_a → saddle points of the corrected L(y, λ) = Φ(y) − Σ_k λ^k (Σ_a y^k_a − γ^k) − Σ_k Σ_a λ^k_a y^k_a; reason: the printed L has no saddle points (see CorrWardrop.kkt_iff_saddle), which would make the statement vacuous
--   - generalization: Φ the convex potential of Γ and U its open convex domain → arbitrary Φ and arbitrary set U; reason: the exchange property of saddle points holds for every function on a product of sets; it specializes to the page's case
-- source:
--   Koessler–Scarsini–Tomala, Correlated Equilibria in Large Anonymous Bayesian Games, arXiv:2107.06312v4, proof of Proposition 4, "From the exchange property …", p.19

import Mathlib
import Definitions.Def_CorrWardrop_Model
import Definitions.Def_CorrWardrop_Lagrangian
open MeasureTheory

namespace CorrWardrop

/-- Proof of Proposition 4, exchange property of saddle points: if `(ŷ, λ̂)` and `(ȳ, λ̄)` are
saddle points of the Lagrangian on `U × (ℝ^K × ℝ_{≥0}^{⊔A^k})`, then `(ŷ, λ̄)` and `(ȳ, λ̂)`
are also saddle points.

Koessler–Scarsini–Tomala, arXiv:2107.06312v4, proof of Proposition 4, p.19.

Formalization Note: `L` is the corrected Lagrangian `lagrangian` (see `IsSaddle`). The exchange
property holds for any `Φ` and any `U`; no hypothesis on `Φ` is needed. -/
theorem saddle_exchange {K : Type*} [Fintype K] {A : K → Type*} [∀ k, Fintype (A k)]
    [DecidableEq K] [∀ k, DecidableEq (A k)]
    (Γ : NonatomicGame K A) (Φ : Flow A → ℝ) (U : Set (Flow A))
    (y₁ y₂ : Flow A) (l₁ l₂ : Multipliers A)
    (h₁ : IsSaddle Γ Φ U y₁ l₁) (h₂ : IsSaddle Γ Φ U y₂ l₂) :
    IsSaddle Γ Φ U y₁ l₂ ∧ IsSaddle Γ Φ U y₂ l₁ := by sorry

end CorrWardrop
