-- Prove2me | Theorems.Thm_ExtraConsensus_Sublinear_proposition_2_2
-- name    : ExtraConsensus.Sublinear.proposition_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:17:28.79161+00:00
-- url     : https://prove2.me/theorems/366e1c6d-df0d-451e-944b-44fe27c4f00b
-- title:
--   Proposition 2.2, p. 7 — parts 2–4 of Assumption 1 give null{I − W} = span{1} and eigenvalues of W in (−1, 1]
-- statement:
--   Let $W,\tilde W\in\mathbb R^{n\times n}$ satisfy parts 2–4 of Assumption 1: $W$ and $\tilde W$ are symmetric, $\operatorname{null}\{W-\tilde W\}=\operatorname{span}\{\mathbf 1\}$, $(I-\tilde W)\mathbf 1=0$, $\tilde W\succ0$ and $\frac{I+W}{2}\succeq\tilde W\succeq W$. Then
--   $$\operatorname{null}\{I-W\}=\operatorname{span}\{\mathbf 1\},\qquad \text{every eigenvalue of }W\text{ lies in }(-1,1].$$
--
--   These are the conditions commonly imposed on the mixing matrix of decentralized gradient descent (DGD), so the additional requirements of EXTRA are on $\tilde W$ only.
--
--   **Formalization Note** Neither the decentralized property (part 1) nor connectivity is assumed. Eigenvalues are real eigenvalues with real eigenvectors, which for the symmetric $W$ are all of them.
-- source:
--   Shi, Ling, Wu & Yin, arXiv:1404.6264v4, Proposition 2.2, p. 7

import Mathlib
import Definitions.Def_ExtraConsensus_Sublinear_Model

namespace ExtraConsensus.Sublinear

open Matrix Filter Topology Asymptotics

/-- Proposition 2.2, p. 7. Parts 2–4 of Assumption 1 (symmetry, null space property, spectral
property; neither the decentralized property nor connectivity) imply `null{I − W} = span{𝟏}` and
that every eigenvalue of `W` lies in `(−1, 1]`. -/
theorem proposition_2_2 {n : ℕ} (W Wt : Matrix (Fin n) (Fin n) ℝ)
    (hWs : Wᵀ = W) (hWts : Wtᵀ = Wt)
    (hnull : ∀ v : Fin n → ℝ, (W - Wt) *ᵥ v = 0 ↔ ∃ c : ℝ, v = fun _ => c)
    (hnull1 : (1 - Wt) *ᵥ (fun _ => (1 : ℝ)) = 0)
    (hpd : Wt.PosDef) (hpsd1 : ((1 / 2 : ℝ) • (1 + W) - Wt).PosSemidef)
    (hpsd2 : (Wt - W).PosSemidef) :
    (∀ v : Fin n → ℝ, (1 - W) *ᵥ v = 0 ↔ ∃ c : ℝ, v = fun _ => c) ∧
      ∀ μ, IsEigenvalue W μ → -1 < μ ∧ μ ≤ 1 := by sorry

end ExtraConsensus.Sublinear
