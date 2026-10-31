-- Prove2me | Theorems.Thm_CapacityGames_support_eq_contributors
-- name    : CapacityGames.support_eq_contributors
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:37:33.640055+00:00
-- url     : https://prove2.me/theorems/a663d77f-2b29-4b7c-9e42-6ab37b35532a
-- title:
--   (5): under Assumption 2, every supply chain optimal choice has support $I(t^*_N)=N^*(\mathcal C)$
-- statement:
--   Consider a capacity game in which every supply chain maximum $\Pi^*_{\mathcal C}(S)$ is attained and Assumption 2 (Uniqueness of Support) holds: all supply chain optimal choices for $N$ use the same set of suppliers. Let $(t^*_N,s^*_N)$ be any supply chain optimal choice, i.e. a feasible choice with $\Pi_{\mathcal C}(t^*_N,s^*_N)=\Pi^*_{\mathcal C}(N)$. Then
--   $$I(t^*_N)=N^*(\mathcal C)=\{j\in N:\Pi^*_{\mathcal C}(N)>\Pi^*_{\mathcal C}(N\setminus\{j\})\}.\quad(5)$$
--
--   The suppliers used in a supply chain optimal choice are exactly those whose removal strictly lowers the optimal supply chain profit. In the proof of Theorem 2 this identifies the suppliers who are paid a margin when the buyer chooses $(t^*_N,s^*_N)$.
--
--   Differences from the source:
--   - generalization: assumptions (a)–(c), p.8 → attainment of every $\Pi^*_{\mathcal C}(S)$ assumed directly; reason: (a)–(c) are made "to ensure that the maxima exist and are attained" and serve no other purpose.
--   - reading: expectations taken without comment → integrability of $V(D,s(D))$ and $C_i(s(D))$ is part of feasibility; reason: the paper writes these expectations, which presupposes them.
--   - encoding: $N=\{1,\dots,n\}$, $I(t)=\{i:t_i>0\}$ → a finite type $N$, $I(t)=\{i:t_i\ne0\}$, $\Pi^*_{\mathcal C}$ as a supremum; reason: equal on $\mathbf T$ because $T_i\subseteq\mathbb R_+$; Lean convention.
-- source:
--   Anderson–Chen–Shao, Capacity Games with Supply Function Competition, arXiv:1905.11084v1, §4, display (5), p.10

import Mathlib
import Definitions.Def_CapacityGames_SetFunction
import Definitions.Def_CapacityGames_Model

open MeasureTheory

namespace CapacityGames

/-- **The optimal support is the set of contributing suppliers**, display (5),
arXiv:1905.11084v1, §4, p.10: under Assumption 2 (and attainment of the maxima (4)), every supply
chain optimal choice `(t*_N, s*_N)` has `I(t*_N) = N*(𝒞)`.

**Formalization Note.** A supply chain optimal choice for `N` is a choice feasible for the supply
chain with `Π_C = Π*_C(N)`. -/
theorem support_eq_contributors {N Ω : Type*} [Fintype N] [DecidableEq N] [MeasurableSpace Ω]
    (G : CapacityGame N Ω) (hG : G.IsValid)
    (hatt : ∀ S : Finset N, SCAttained G S) (huniq : UniqueSupport G)
    (p : Choice N Ω) (hp : SCFeasible G p) (hopt : scProfit G p = scOptValue G Finset.univ) :
    support p.t = contributors G := by sorry

end CapacityGames
