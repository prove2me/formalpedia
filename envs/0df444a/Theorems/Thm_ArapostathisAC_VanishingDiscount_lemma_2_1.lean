-- Prove2me | Theorems.Thm_ArapostathisAC_VanishingDiscount_lemma_2_1
-- name    : ArapostathisAC.VanishingDiscount.lemma_2_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T07:40:54.942984+00:00
-- url     : https://prove2.me/theorems/a6db2ffc-8167-4612-91a7-5636fbcaff25
-- title:
--   Lemma 2.1 — the dynamic programming map commutes with constants and is monotone
-- statement:
--   Consider the countable-state controlled Markov process of §5 and its undiscounted dynamic programming map
--   $$T(v)(i)=\inf_{a\in U(i)}\Big\{c(i,a)+\sum_{j\in S}P(j\mid i,a)\,v(j)\Big\}.$$
--   Let $v,v':S\to\mathbb R$ be bounded below, and assume that every series $\sum_j P(j\mid i,a)v(j)$ and $\sum_j P(j\mid i,a)v'(j)$, $i\in S$, $a\in U(i)$, converges. Then
--
--   1. for every $k\in\mathbb R$, $T(v+k)=T(v)+k$;
--   2. if $v\le v'$ pointwise, then $T(v)\le T(v')$.
--
--   These two properties are the elementary tools used to pass from the discounted optimality equation for $J^*_\beta$ to the equation (5.6) for the differential value function $h_\beta$.
--
--   **Formalization Note.** The paper states the lemma for $v,v'\in\mathcal L(S)$, the lower semicontinuous functions bounded below. On the discrete space $S=\mathbb N$ every function is lower semicontinuous, so $\mathcal L(S)$ is the set of functions bounded below. The paper leaves the convergence of the series implicit; it is a stated hypothesis here because Lean's `tsum` of a non-summable family is $0$.
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), p. 289, Lemma 2.1 and (2.5)

import Mathlib
import Definitions.Def_ArapostathisAC_VanishingDiscount_CMP
import Definitions.Def_ArapostathisAC_VanishingDiscount_DPMaps

namespace ArapostathisAC.VanishingDiscount

theorem lemma_2_1 {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
    (M : CMP A) (v v' : ℕ → ℝ) (hv : BddBelow (Set.range v)) (hv' : BddBelow (Set.range v'))
    (hsv : ∀ i, ∀ a ∈ M.U i, Summable (fun j => prob M i a j * v j))
    (hsv' : ∀ i, ∀ a ∈ M.U i, Summable (fun j => prob M i a j * v' j)) :
    (∀ k : ℝ, bellmanT M (fun j => v j + k) = fun i => bellmanT M v i + k) ∧
    (v ≤ v' → bellmanT M v ≤ bellmanT M v') := by sorry

end ArapostathisAC.VanishingDiscount
