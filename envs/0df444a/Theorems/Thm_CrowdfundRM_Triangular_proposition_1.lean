-- Prove2me | Theorems.Thm_CrowdfundRM_Triangular_proposition_1
-- name    : CrowdfundRM.Triangular.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:50:14.443466+00:00
-- url     : https://prove2.me/theorems/8029c1a2-4255-4535-85f0-52027658e879
-- title:
--   Proposition 1, p. 8 — every solution of the independent backers' pledging system (1)–(4) is the closed form (5)–(7)
-- statement:
--   Consider a campaign satisfying the standing assumptions, a pledge level $p$ and a duration $T\ge0$. Let $(n_i, n^p_i, n^l_i)$ be any solution on $[0,T]$ of the independent backers' system (1)–(4) (in integral form: continuous functions with $n^p_i(t)=\int_0^t k(\hat I-n_i)\bar F_i(pe^{r(T-s)})ds$, $n^l_i(t)=\int_0^t k(\hat I-n_i)(1-\bar F_i(pe^{r(T-s)}))ds$, $n_i=n^p_i+n^l_i$). Then for every $t\in[0,T]$,
--   $$n^p_i(t)=k\hat I\int_0^t e^{-kx}\bar F_i(pe^{r(T-x)})\,dx,\qquad n^l_i(t)=k\hat I\int_0^t e^{-kx}\bigl(1-\bar F_i(pe^{r(T-x)})\bigr)dx,\qquad n_i(t)=\hat I(1-e^{-kt}).$$
--   Conversely, these three closed forms solve the system on $[0,T]$.
--
--   The closed form (5) is the independent backers' contribution to the total number of pledges and enters every later result.
--
--   **Formalization Note** "The solution is given by" is stated as uniqueness (every solution equals the closed forms) together with existence (the closed forms are a solution). The paper writes $1-F_i$; the formalization writes $\bar F_i$ throughout, with $F_i=1-\bar F_i$.
-- source:
--   Zhang, Savin, Veeraraghavan, Revenue Management in Crowdfunding, SSRN 3065267 (manuscript of May 26, 2021), p. 8, Proposition 1, (1)–(7)

import Mathlib
import Definitions.Def_CrowdfundRM_Triangular_Setting

namespace CrowdfundRM.Triangular
theorem proposition_1 (M : Campaign) (hM : M.Standing) (p T : ℝ) (hT : 0 ≤ T) :
    (∀ ni np nl : ℝ → ℝ, M.IndepSol p T ni np nl →
      ∀ t ∈ Set.Icc 0 T, np t = M.npi p T t ∧ nl t = M.nli p T t ∧
        ni t = M.Ihat * (1 - Real.exp (-M.k * t))) ∧
    M.IndepSol p T (fun t => M.Ihat * (1 - Real.exp (-M.k * t))) (M.npi p T) (M.nli p T) := by sorry
end CrowdfundRM.Triangular
