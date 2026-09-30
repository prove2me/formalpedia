-- Prove2me | Theorems.Thm_BayesRouting_VOI_thresholds_admissible
-- name    : BayesRouting.VOI.thresholds_admissible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T15:05:38.799702+00:00
-- url     : https://prove2.me/theorems/5185fc6b-bf6d-4044-bbe3-399cf0cbb77e
-- title:
--   Lemma 4 — $0\le\underline\lambda^i\le\overline\lambda^i\le 1-|\lambda^{-ij}|$
-- statement:
--   Let $i\ne j$ be two populations and $\lambda$ a size vector in the simplex with $\lambda^i>0$ and $\lambda^j>0$. The thresholds (23) built from the optimal set $\mathcal F^{ij,\dagger}$ of (OPT-$\mathcal F^{ij}$) satisfy
--
--   $$0\le\underline\lambda^i\le\overline\lambda^i\le1-|\lambda^{-ij}|.$$
--
--   Hence the three regimes $\Lambda^{ij}_1,\Lambda^{ij}_2,\Lambda^{ij}_3$ partition the admissible range $\lambda^i\in(0,1-|\lambda^{-ij}|)$ in increasing order of $\lambda^i$.
-- source:
--   Wu, Amin, Ozdaglar, Value of Information in Bayesian Routing Games, Oper. Res. 69(1) 2021, p. 156, Lemma 4

import Mathlib
import Definitions.Def_BayesRouting_VOI_Game
import Definitions.Def_BayesRouting_VOI_Potential
import Definitions.Def_BayesRouting_VOI_Flows
import Definitions.Def_BayesRouting_VOI_Pairwise

namespace BayesRouting.VOI

/-- **Lemma 4** (Wu, Amin, Ozdaglar, Oper. Res. 69(1) 2021, p. 156). For two distinct populations
`i, j` and an admissible size vector (in the simplex, `λ^i > 0`, `λ^j > 0`), the thresholds (23)
satisfy `0 ≤ λ̲^i ≤ λ̄^i ≤ 1 - |λ^{-ij}|`. -/
theorem thresholds_admissible {I : Type} [Fintype I] [DecidableEq I] {T : I → Type} [∀ i, Fintype (T i)]
    [∀ i, DecidableEq (T i)] [∀ i, Nonempty (T i)] {S E R : Type} [Fintype S] [Fintype E]
    [DecidableEq E] [Fintype R] [Nonempty R]
    (G : Game I T S E R) (i j : I) (hij : i ≠ j) (lam : I → ℝ) (hlam : lam ∈ stdSimplex ℝ I)
    (hi : 0 < lam i) (hj : 0 < lam j) :
    0 ≤ lowThr G lam i j ∧ lowThr G lam i j ≤ highThr G lam i j ∧
      highThr G lam i j ≤ 1 - restSize lam i j := by sorry

end BayesRouting.VOI
