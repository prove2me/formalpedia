-- Prove2me | Theorems.Thm_CompDesign_thm_5_1_zero_case
-- name    : CompDesign.thm_5_1_zero_case
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T05:53:30.444789+00:00
-- url     : https://prove2.me/theorems/79c981d9-e800-498f-92d2-d061797e52b4
-- title:
--   Proof of Theorem 5.1 — a pure Nash equilibrium with $v(S)=0$ forces $\mathrm{OPT}=0$
-- statement:
--   Throughout, $N=\{1,\dots,n\}$ is the set of agents, $B>0$ the budget, $c_i\ge 0$ the private costs, and $v:2^N\to\mathbb R$ a value function satisfying Assumption 3.1: $v(\emptyset)=0$, $v$ monotone ($S\subseteq S'\Rightarrow v(S)\le v(S')$) and submodular ($v(S\cup\{i\})-v(S)\ge v(S'\cup\{i\})-v(S')$ whenever $S\subseteq S'$ and $i\notin S'$). The marginal-contribution payment is $p^{mc}_i(S)=B\,\frac{v(S)-v(S\setminus\{i\})}{v(S)}$ if $i\in S$ and $v(S)>0$, and $0$ otherwise (8); agent $i$'s utility is $u_i(S)=p^{mc}_i(S)-c_i$ if $i\in S$ and $0$ otherwise.
--
--   Assume moreover $c_j<B$ for every agent $j$, and let $\mathrm{OPT}=\max\{v(T):T\subseteq N,\ \sum_{i\in T}c_i\le B\}$ (4). If $S$ is a pure Nash equilibrium of $\Gamma^{mc}$ with $v(S)=0$, then
--   $$\mathrm{OPT}=0.$$
--
--   This disposes of the zero-value equilibria in the proof of Theorem 5.1, so that the bound $\mathrm{OPT}\le(1+\kappa(\lambda))v(S)$ holds at them too.
--
--   **Formalization Note** `OPT` is the published `CompDesignBFM.OPT`, a maximum over the budget-feasible sets.
--
--   Differences from the source: none.
-- source:
--   Anagnostides, Bhawalkar, Liaw, Mehta, Paes Leme, Teng, Velegkas, Zheng, Compensation Design, arXiv:2607.14438 (version of November 3, 2026, sha256 3d305d4d…), proof of Theorem 5.1, §5.1, p.27 (PDF 30)

import Mathlib
import Definitions.Def_CompDesignBFM_IsMonotoneSF
import Definitions.Def_CompDesignBFM_IsSubmodularSF
import Definitions.Def_CompDesignBFM_IsPNE
import Definitions.Def_CompDesignBFM_OPT

open CompDesignBFM

namespace CompDesign

/-- Zero-value equilibria, proof of Theorem 5.1, §5.1, p.27 (PDF 30) of Anagnostides et al., *Compensation Design*, arXiv:2607.14438 (version of November 3, 2026, sha256 3d305d4d…):
if a pure Nash equilibrium `S` of `Γ^mc` has `v(S) = 0`, then `OPT = 0`.

**Formalization Note.** Assumption 3.1, `B > 0`, `c ≥ 0` and `c_i < B` for every agent (which the proof
of Theorem 5.1 uses) are binders. `OPT` is (4), `max {v(T) : ∑_{i∈T} c_i ≤ B}`. -/
theorem thm_5_1_zero_case {n : ℕ} (v : Finset (Fin n) → ℝ) (B : ℝ) (c : Fin n → ℝ) (hB : 0 < B)
    (hv0 : v ∅ = 0) (hm : IsMonotoneSF v) (hs : IsSubmodularSF v) (hc : ∀ j, 0 ≤ c j)
    (hcB : ∀ j, c j < B) (S : Finset (Fin n)) (hS : IsPNE v B c S) (hzero : v S = 0) :
    OPT v B c = 0 := by sorry

end CompDesign
