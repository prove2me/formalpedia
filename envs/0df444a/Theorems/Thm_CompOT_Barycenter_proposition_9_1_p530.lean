-- Prove2me | Theorems.Thm_CompOT_Barycenter_proposition_9_1_p530
-- name    : CompOT.Barycenter.proposition_9_1_p530
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:33:43.961989+00:00
-- url     : https://prove2.me/theorems/59cf005c-eff4-4c8d-b421-6a1acceb2a9d
-- title:
--   Proposition 9.1, p. 530 — optimal entropic barycenter scalings and dual value
-- statement:
--   Let $S,n,n_s$ be positive finite sizes. For each source $s$, let $b_s$ be a strictly positive probability histogram on $n_s$ sites and let $C_s$ be a real $n\times n_s$ cost matrix. Let $\lambda$ be a probability vector with every $\lambda_s>0$, and let $\varepsilon>0$. A family of nonnegative couplings is feasible when its column marginals are $b_s$ and its row marginals all agree.
--
--   The KL projection problem (9.16) and the constrained dual program (9.21) both attain their optima. For **every** optimal dual family $(f_s,g_s)_s$ and **every** optimal coupling family $(P_s)_s$,
--   $$\sum_s\lambda_s f_s=0,\qquad P_{s,ij}=e^{f_{s,i}/\varepsilon}K_{s,ij}e^{g_{s,j}/\varepsilon},\quad K_{s,ij}=e^{-C_{s,ij}/\varepsilon}.$$
--   The dual maximum equals the minimum of the weighted entropic transport problem (9.15), evaluated at its optimal couplings:
--   $$\max\,(9.21)=\sum_s\lambda_s\bigl(\langle C_s,P_s\rangle-\varepsilon H(P_s)\bigr).$$
--
--   This connects the barycenter's shared-marginal KL projection, its scaling representation, and the value of the potential program.
--
--   **Formalization Note** `Fin` indices start at zero. The hypotheses $\lambda_s>0$ and $b_{s,j}>0$ ensure that zero-weight couplings and boundary column potentials cannot spoil the assertion about every optimizer. The page's marginal subscripts in (9.16) and the missing subscript on $K$ in (9.17) are corrected. The matrix KL objective differs from the entropic objective by $\varepsilon\sum_s\lambda_s\sum_{i,j}K_{s,ij}$, which also separates the KL dual from (9.21); these constants cancel in the value equality.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), Proposition 9.1 and (9.21), p. 530; (9.15)–(9.17), p. 529

import Mathlib
import Definitions.Def_CompOT_Barycenter_Defs

namespace CompOT.Barycenter

/-- Proposition 9.1 on p. 530 (the barycenter result, distinct from the
Proposition 9.1 on p. 519). The common optimizer of (9.16) has the
scaling form (9.17) for every solution of (9.21), and the values of
(9.21) and (9.15) agree. -/
theorem proposition_9_1_p530 {S n : ℕ} (ns : Fin S → ℕ)
    (hS : 0 < S) (hn : 0 < n) (hns : ∀ s, 0 < ns s)
    (ε : ℝ) (hε : 0 < ε)
    (C : (s : Fin S) → Matrix (Fin n) (Fin (ns s)) ℝ)
    (b : (s : Fin S) → Fin (ns s) → ℝ)
    (hb : ∀ s, b s ∈ stdSimplex ℝ (Fin (ns s)))
    (hbpos : ∀ s j, 0 < b s j)
    (weights : Fin S → ℝ)
    (hw : weights ∈ stdSimplex ℝ (Fin S))
    (hwpos : ∀ s, 0 < weights s) :
    ∃ (P : (s : Fin S) → Matrix (Fin n) (Fin (ns s)) ℝ)
      (f : Fin S → Fin n → ℝ)
      (g : (s : Fin S) → Fin (ns s) → ℝ),
      IsBarycenterKLOptimal ns ε C b weights P ∧
      IsBarycenterDualOptimal ns ε C b weights f g ∧
      barycenterDualObjective ns ε C b weights f g =
        barycenterPrimalObjective ns ε C weights P ∧
      ∀ f' g', IsBarycenterDualOptimal ns ε C b weights f' g' →
        ∀ Q, IsBarycenterKLOptimal ns ε C b weights Q →
          ∀ s i j, Q s i j =
            Real.exp (f' s i / ε) * gibbs ε (C s) i j *
              Real.exp (g' s j / ε) := by sorry

end CompOT.Barycenter
