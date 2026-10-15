-- Prove2me | Theorems.Thm_DynReinsDiv_HJB_lemma_A_3
-- name    : DynReinsDiv.HJB.lemma_A_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:35:22.381986+00:00
-- url     : https://prove2.me/theorems/4b262095-f5b2-4772-a545-55e98ac5f978
-- title:
--   Lemma A.3 — (A.17) has a C^{2,1} solution u^ε, and 1 ≤ u^ε ≤ Ke^{Λt}/(x + 1/λ) for small ε, K = L + 1/λ + 1, Λ = μ₂/γ² + γλ
-- statement:
--   Fix a model, $L>0$ and the positive root $\lambda$ of $f$. There is $\varepsilon_0>0$ such that for every $\varepsilon\in(0,\varepsilon_0)$, every penalty function $\beta_\varepsilon$ and every boundary datum $f_\varepsilon$, the penalized problem (A.17) has a solution $u^\varepsilon\in C^{2,1}(\overline{\mathcal Q}_{L,T})$, and this solution satisfies
--   $$1\le u^\varepsilon(x,t)\le\frac{K e^{\Lambda t}}{x+1/\lambda}\quad\text{in }\mathcal Q_{L,T},\qquad K=L+\frac1\lambda+1,\quad \Lambda=\frac{\mu_2}{\gamma^2}+\gamma\lambda . \tag{A.19}$$
--
--   The lower bound puts $u^\varepsilon$ in the range where Lemma A.1 and the comparison principle apply; the upper bound, together with Lemmas A.4 and A.5, gives estimates on $u^\varepsilon$ and $u^\varepsilon_x$ that do not depend on $\varepsilon$.
--
--   **Formalization Note** The paper introduces $\beta_\varepsilon$ and $f_\varepsilon$ only "for each sufficiently small $\varepsilon>0$" (p. 24), so existence and the bound are both asserted for $\varepsilon\in(0,\varepsilon_0)$ and every admissible $\beta_\varepsilon$, $f_\varepsilon$; $\varepsilon_0>0$ is chosen before $\beta_\varepsilon$ and $f_\varepsilon$, and may depend on the model, $L$ and $\lambda$. A solution is required to be nonzero in $\mathcal Q_{L,T}$ so that $\mathcal Tu$ is defined.
-- source:
--   Guan, Xu & Zhou, Dynamic optimal reinsurance and dividend-payout in a finite time horizon, arXiv:2008.00391v3, pp. 26–27, Lemma A.3 and (A.19)

import Mathlib
import Definitions.Def_DynReinsDiv_HJB_Model
import Definitions.Def_DynReinsDiv_HJB_PDE

namespace DynReinsDiv.HJB

theorem lemma_A_3 (M : Model) (L lam : ℝ) (hL : 0 < L) (hlam : 0 < lam)
    (hroot : M.fA lam = 0) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ β fε : ℝ → ℝ, IsPenalty M ε β → IsRamp ε lam fε →
      ∃ u ux uxx ut : ℝ → ℝ → ℝ, IsC21RectClosed L M.T u ux uxx ut ∧
        SolvesPenalized M L lam β fε u ux uxx ut ∧
        ∀ x t : ℝ, 0 < x → x < L → 0 < t → t ≤ M.T →
          1 ≤ u x t ∧
          u x t ≤ (L + 1 / lam + 1) * Real.exp ((M.μ₂ / M.γ ^ 2 + M.γ * lam) * t) / (x + 1 / lam) := by sorry

end DynReinsDiv.HJB
