-- Prove2me | Theorems.Thm_DealerDissem_RankFree_proof_thm1_psi_contraction
-- name    : DealerDissem.RankFree.proof_thm1_psi_contraction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:02:12.617985+00:00
-- url     : https://prove2.me/theorems/24f84e04-a34e-4070-82ac-bca8bd2c84cf
-- title:
--   Proof of Theorem 1, pp. 39–40 — on $\mathcal F_+$ the max in (46) is reached, $\Psi$ maps $\mathcal F_+$ into itself and is a $q$-contraction
-- statement:
--   Throughout, $\rho>0$ is the sure return of the asset, $r>0$ the funding spread, $q\in(0,1)$ the probability that a dealer is available, and $G$ the distribution of the customer demand $\tilde\omega$, a probability distribution on $\mathbb R_+$ with finite mean; $H(\omega)=\Pr(\tilde\omega\ge\omega)$. For a function $\beta$ define, as in (46),
--   $$\Psi(\beta)(y)=\max_{0\le\omega\le y} qH(\omega)\bigl(\omega+\beta(y-\omega)\bigr).$$
--   Let $\mathcal F_+$ be the set of functions $\beta$ that are bounded and continuous on $\mathbb R_+$, non-negative on $\mathbb R_+$, with $\beta(0)=0$. Then:
--
--   1. for every $\beta\in\mathcal F_+$ and every $y\ge0$ the supremum defining $\Psi(\beta)(y)$ is attained at some $\omega\in[0,y]$, and $\Psi(\beta)\in\mathcal F_+$;
--   2. for $\beta_1,\beta_2\in\mathcal F_+$ and any $C$ with $|\beta_1(y)-\beta_2(y)|\le C$ for all $y\ge0$,
--   $$|\Psi(\beta_1)(y)-\Psi(\beta_2)(y)|\le qC\qquad(y\ge0),$$
--   that is, $\|\Psi(\beta_1)-\Psi(\beta_2)\|_\infty\le q\|\beta_1-\beta_2\|_\infty$.
--
--   This is the contraction step of the proof of Theorem 1: the collected demand is the fixed point of $\Psi$. $H$ may be discontinuous ($G$ may have atoms).
--
--   **Formalization Note.** The paper works on the space $\mathcal F$ of bounded continuous $\beta$ with $\beta(0)=0$ and checks Blackwell's conditions. The statement here is restricted to the non-negative members $\mathcal F_+$: for a $\beta$ with negative values, $H(\omega)(\omega+\beta(y-\omega))$ need not be upper semicontinuous and the attainment and continuity claims can fail, while every solution of (9) is non-negative (take $\omega=0$), so nothing downstream is lost. The contraction is stated directly in sup-norm form rather than through Blackwell's conditions.
-- source:
--   Colliard & Demange, Asset Dissemination through Dealer Markets, SSRN 3244321 (authors' version of September 17, 2020), pp. 39–40 (PDF 41–42), proof of Theorem 1, (46), (47)

import Mathlib
import Definitions.Def_DealerDissem_RankFree_Model

open MeasureTheory

namespace DealerDissem.RankFree

/-- Proof of Theorem 1, pp. 39–40: on `𝓕₊`, the max in (46) is reached, `Ψ` maps `𝓕₊`
into `𝓕₊`, and `Ψ` is a `q`-contraction for the sup-norm on `ℝ₊`. -/
theorem proof_thm1_psi_contraction (P : Params) (μ : Measure ℝ) (hμ : IsDemandDist μ) :
    (∀ β : ℝ → ℝ, InFPlus β →
        (∀ y, 0 ≤ y → ∃ ω ∈ Set.Icc 0 y, Psi P μ β y = objective P μ β y ω) ∧
        InFPlus (Psi P μ β)) ∧
    (∀ β₁ β₂ : ℝ → ℝ, InFPlus β₁ → InFPlus β₂ → ∀ C : ℝ,
        (∀ y, 0 ≤ y → |β₁ y - β₂ y| ≤ C) →
        ∀ y, 0 ≤ y → |Psi P μ β₁ y - Psi P μ β₂ y| ≤ P.q * C) := by sorry

end DealerDissem.RankFree
