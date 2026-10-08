-- Prove2me | Theorems.Thm_BestBothWorlds_SAO_sum_q_le_harmonic
-- name    : BestBothWorlds.SAO.sum_q_le_harmonic
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T02:47:15.254884+00:00
-- url     : https://prove2.me/theorems/5292263e-7c64-49aa-85a6-10c0d53a33c1
-- title:
--   (27) — $\sum_{i=1}^K q_i\le1+\log K$
-- statement:
--   Let $K\ge2$, $n\ge K$ and $\beta>1$. On every run of SAO with parameter $\beta$, against any adaptive adversary whose rewards lie in $[0,1]$ and along any arm path,
--   $$\sum_{i=1}^K q_i\le1+\log K,$$
--   where $q_i=p_{i,\min(\tau_i,\tau_0)}$ is the probability of arm $i$ when it was deactivated (or at time $\tau_0$, if Exp3.P started before arm $i$ was deactivated).
--
--   Active arms share their probability equally. The arm deactivated $j$-th therefore had probability at most $1/(K-j+1)$, and the sum is at most the harmonic number $H_K\le1+\log K$. This bound is the source of the factor $1+\log K$ in both halves of Theorem 4.1.
-- source:
--   Bubeck & Slivkins, The best of both worlds: stochastic and adversarial bandits, arXiv:1202.4473v1, p. 18, §4.2, eq. (27)

import Mathlib
import Definitions.Def_BestBothWorlds_SAO_Interaction
import Definitions.Def_BestBothWorlds_SAO_Exp3P
import Definitions.Def_BestBothWorlds_SAO_Algorithm
import Definitions.Def_BestBothWorlds_SAO_RunNotation

open MeasureTheory

namespace BestBothWorlds.SAO

/-- §4.2, (27) (p. 18): on every run of SAO with parameter `β > 1`, against bounded rewards and
along any arm path, `∑_{i=1}^K q_i ≤ 1 + log K`, where `q_i = p_{i, min(τ_i, τ₀)}`. -/
theorem sum_q_le_harmonic (K n : ℕ) (hK : 2 ≤ K) (hKn : K ≤ n) (β : ℝ) (hβ : 1 < β)
    (adv : Adversary K) (hadv : adv.IsBounded) (I : Fin n → Fin K) :
    ∑ i : Fin K, qEff K n β adv I i ≤ 1 + Real.log K := by sorry

end BestBothWorlds.SAO
