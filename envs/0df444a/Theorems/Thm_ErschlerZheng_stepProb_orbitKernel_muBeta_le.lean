-- Prove2me | Theorems.Thm_ErschlerZheng_stepProb_orbitKernel_muBeta_le
-- name    : ErschlerZheng.stepProb_orbitKernel_muBeta_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T07:08:41.243527+00:00
-- url     : https://prove2.me/theorems/a4bc6883-cd6f-4262-b4db-e67764ca52e7
-- title:
--   Proposition 7.19 — sup_{x,y} P^t_{μ_β}(x, y) ⩽ C/t^{1/β} on 1^∞·G_ω
-- statement:
--   Let $1 - \frac1D < \beta < 1$. Then there is a constant $C$ such that for every string $\omega$ satisfying Assumption $(\mathrm{Fr}(D))$ (`SatisfiesFr`), every sequence $(k_n)$ satisfying the standing assumption of p. 40 (`IsAdmissibleSeq`), every $t \ge 1$ and all $x, y$ in the orbit $1^\infty \cdot G_\omega$ (`orbitOne`), the $t$-step transition probability (`DurrettProbability.stepProb`) of the kernel induced on the orbit by the measure $\mu_\beta$ (`muBeta`) built with $(k_n)$ satisfies $P^t_{\mu_\beta}(x, y) \le C/t^{1/\beta}$.
--
--   Erschler and Zheng, p. 48, Proposition 7.19: “Let $P_{\mu_\beta}$ be the transition kernel on $1^\infty \cdot G_\omega$ induced by $\mu_\beta$. Then there exists a constant $C = C(\beta) < \infty$ such that for $t \in \mathbb N$, $\sup_{x,y \in 1^\infty \cdot G} P^t_{\mu_\beta}(x, y) \leqslant \frac{C}{t^{1/\beta}}$.”
--
--   The subsection fixes $k_n = A\lfloor\log_2 n\rfloor$ (p. 48: “Throughout this subsection $\beta \in (1 - \frac1D, 1)$ and $k_n = A\lfloor\log_2 n\rfloor$, and the measure $\mu_\beta$ is defined in (7.11).”). The statement takes every admissible $(k_n)$, that choice included, with the constant chosen before $\omega$ and $(k_n)$, as the sentence before the proposition says: “The following on-diagonal upper bound does not depend on the choice of $(k_n)$”. The constant may depend on $D$, which fixes the range of $\beta$. The bound is asserted for $t \ge 1$, where the printed right side $C/t^{1/\beta}$ is defined. The supremum is written as the bound for every pair $x, y$.
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 48, Proposition 7.19

import Mathlib
import Definitions.Def_ErschlerZheng_Construction
import Definitions.Def_DurrettProbability_MarkovChain

namespace ErschlerZheng

theorem stepProb_orbitKernel_muBeta_le (D : ℕ) (β : ℝ) (hβ1 : 1 - 1 / (D : ℝ) < β)
    (hβ2 : β < 1) :
    ∃ C : ℝ, ∀ ω : ℕ → Fin 3, SatisfiesFr D ω → ∀ [DecidableEq (orbitOne ω)],
      ∀ k : ℕ → ℕ, IsAdmissibleSeq D k → ∀ t : ℕ, 1 ≤ t → ∀ x y : orbitOne ω,
        DurrettProbability.stepProb (orbitKernel (grigorchuk ω) (muBeta D ω k β) oneRay)
          t x y ≤ C / (t : ℝ) ^ (1 / β) := by
  sorry

end ErschlerZheng
