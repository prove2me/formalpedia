-- Prove2me | Theorems.Thm_CompDesign_eq_24
-- name    : CompDesign.eq_24
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T05:53:45.250997+00:00
-- url     : https://prove2.me/theorems/96796701-8661-4d89-a741-2646ad4e493f
-- title:
--   (24) — at an equilibrium with $v(S)>0$, $v(T)\le v(S)\big(1+\sum_{i\in T\setminus S}\frac{x_i}{1-x_i}\big)$
-- statement:
--   Throughout, $N=\{1,\dots,n\}$ is the set of agents, $B>0$ the budget, $c_i\ge 0$ the private costs, and $v:2^N\to\mathbb R$ a value function satisfying Assumption 3.1: $v(\emptyset)=0$, $v$ monotone ($S\subseteq S'\Rightarrow v(S)\le v(S')$) and submodular ($v(S\cup\{i\})-v(S)\ge v(S'\cup\{i\})-v(S')$ whenever $S\subseteq S'$ and $i\notin S'$). The marginal-contribution payment is $p^{mc}_i(S)=B\,\frac{v(S)-v(S\setminus\{i\})}{v(S)}$ if $i\in S$ and $v(S)>0$, and $0$ otherwise (8); agent $i$'s utility is $u_i(S)=p^{mc}_i(S)-c_i$ if $i\in S$ and $0$ otherwise.
--
--   Assume moreover $c_j<B$ for every agent $j$, and write $x_i=c_i/B$. Let $S$ be a pure Nash equilibrium of $\Gamma^{mc}$ with $v(S)>0$. Then for every set $T\subseteq N$,
--   $$v(T)\le v(S)\Big(1+\sum_{i\in T\setminus S}\frac{x_i}{1-x_i}\Big).\tag{24}$$
--
--   Applied to an optimal budget-feasible set $T=S^*$, the vector $(x_i)_{i\in S^*\setminus S}$ is feasible in the definition (20) of $\kappa(\lambda)$, which gives Theorem 5.1.
--
--   Differences from the source:
--   - generalization: T = S* ∈ arg max{v(T) : ∑_{i∈T} c_i ≤ B} → every set T; reason: (24) combines (23) with the union bound and uses neither the optimality nor the budget feasibility of S*; S* is an instance
-- source:
--   Anagnostides, Bhawalkar, Liaw, Mehta, Paes Leme, Teng, Velegkas, Zheng, Compensation Design, arXiv:2607.14438 (version of November 3, 2026, sha256 3d305d4d…), proof of Theorem 5.1, §5.1, eq. (24), p.27 (PDF 30)

import Mathlib
import Definitions.Def_CompDesignBFM_IsMonotoneSF
import Definitions.Def_CompDesignBFM_IsSubmodularSF
import Definitions.Def_CompDesignBFM_IsPNE

open CompDesignBFM

namespace CompDesign

/-- Display (24), proof of Theorem 5.1, §5.1, p.27 (PDF 30) of Anagnostides et al., *Compensation Design*, arXiv:2607.14438 (version of November 3, 2026, sha256 3d305d4d…):
for a pure Nash equilibrium `S` of `Γ^mc` with `v(S) > 0`, and `x_i = c_i/B`,
`v(T) ≤ v(S) (1 + ∑_{i∈T∖S} x_i/(1 − x_i))`.

**Formalization Note.** The paper states (24) for an optimal set `T = S*`; it is stated for every set
`T`. Assumption 3.1, `B > 0`, `c ≥ 0` and `c_i < B` for every agent are binders. -/
theorem eq_24 {n : ℕ} (v : Finset (Fin n) → ℝ) (B : ℝ) (c : Fin n → ℝ) (hB : 0 < B)
    (hv0 : v ∅ = 0) (hm : IsMonotoneSF v) (hs : IsSubmodularSF v) (hc : ∀ j, 0 ≤ c j)
    (hcB : ∀ j, c j < B) (S : Finset (Fin n)) (hS : IsPNE v B c S) (hpos : 0 < v S)
    (T : Finset (Fin n)) :
    v T ≤ v S * (1 + ∑ i ∈ T \ S, (c i / B) / (1 - c i / B)) := by sorry

end CompDesign
