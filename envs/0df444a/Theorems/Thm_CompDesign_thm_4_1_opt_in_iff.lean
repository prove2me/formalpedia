-- Prove2me | Theorems.Thm_CompDesign_thm_4_1_opt_in_iff
-- name    : CompDesign.thm_4_1_opt_in_iff
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T05:58:14.190325+00:00
-- url     : https://prove2.me/theorems/725a6b76-0a8e-4920-afa7-63f5447eb6e5
-- title:
--   Proof of Theorem 4.1 — strictly profitable opt-in $\iff (1-c_i/B)\,v(S\cup\{i\})>v(S)$
-- statement:
--   Throughout, $N=\{1,\dots,n\}$ is the set of agents, $B>0$ the budget, $c_i\ge 0$ the private costs, and $v:2^N\to\mathbb R$ a value function satisfying Assumption 3.1: $v(\emptyset)=0$, $v$ monotone ($S\subseteq S'\Rightarrow v(S)\le v(S')$) and submodular ($v(S\cup\{i\})-v(S)\ge v(S'\cup\{i\})-v(S')$ whenever $S\subseteq S'$ and $i\notin S'$). The marginal-contribution payment is $p^{mc}_i(S)=B\,\frac{v(S)-v(S\setminus\{i\})}{v(S)}$ if $i\in S$ and $v(S)>0$, and $0$ otherwise (8); agent $i$'s utility is $u_i(S)=p^{mc}_i(S)-c_i$ if $i\in S$ and $0$ otherwise.
--
--   Assume moreover $c_j<B$ for every agent $j$ (the hypothesis of Theorem 4.1). Let $i\notin S$. Then:
--
--   1. if opting in is strictly profitable, $u_i(S\cup\{i\})>u_i(S)$, then $v(S\cup\{i\})>0$;
--   2. opting in is strictly profitable if and only if $c_i<p^{mc}_i(S\cup\{i\})$;
--   3. if $v(S\cup\{i\})>0$, then
--   $$B\,\frac{v(S\cup\{i\})-v(S)}{v(S\cup\{i\})}>c_i \iff \Big(1-\frac{c_i}{B}\Big)v(S\cup\{i\})>v(S).$$
--
--   This is the opt-in case of the potential argument for Theorem 4.1: a strictly profitable opt-in raises $\Phi$.
--
--   Differences from the source: none.
-- source:
--   Anagnostides, Bhawalkar, Liaw, Mehta, Paes Leme, Teng, Velegkas, Zheng, Compensation Design, arXiv:2607.14438 (version of November 3, 2026, sha256 3d305d4d…), proof of Theorem 4.1, §4.1, p.17 (PDF 20)

import Mathlib
import Definitions.Def_CompDesignBFM_IsMonotoneSF
import Definitions.Def_CompDesignBFM_IsSubmodularSF
import Definitions.Def_CompDesignBFM_mcPay
import Definitions.Def_CompDesign_util

open CompDesignBFM

namespace CompDesign

/-- Opt-in equivalence, proof of Theorem 4.1, §4.1, p.17 (PDF 20) of Anagnostides et al., *Compensation Design*, arXiv:2607.14438 (version of November 3, 2026, sha256 3d305d4d…).
For an agent `i ∉ S`: a strictly profitable opt-in needs `v(S ∪ {i}) > 0`; it is strictly profitable
iff `B (v(S ∪ {i}) − v(S))/v(S ∪ {i}) > c_i`; and, when `v(S ∪ {i}) > 0`, this holds iff
`(1 − c_i/B) v(S ∪ {i}) > v(S)`.

**Formalization Note.** The standing assumptions (Assumption 3.1, `B > 0`, `c ≥ 0`) and the hypothesis
`max_i c_i < B` of Theorem 4.1 are kept as binders. The payment at `S ∪ {i}` is `mcPay`, which for
`v(S ∪ {i}) > 0` is `B (v(S ∪ {i}) − v(S))/v(S ∪ {i})` since `(S ∪ {i}) ∖ {i} = S`. -/
theorem thm_4_1_opt_in_iff {n : ℕ} (v : Finset (Fin n) → ℝ) (B : ℝ) (c : Fin n → ℝ) (hB : 0 < B)
    (hv0 : v ∅ = 0) (hm : IsMonotoneSF v) (hs : IsSubmodularSF v) (hc : ∀ j, 0 ≤ c j)
    (hcB : ∀ j, c j < B) (S : Finset (Fin n)) (i : Fin n) (hi : i ∉ S) :
    (util v B c S i < util v B c (insert i S) i → 0 < v (insert i S)) ∧
    (util v B c S i < util v B c (insert i S) i ↔ c i < mcPay v B (insert i S) i) ∧
    (0 < v (insert i S) →
      (c i < mcPay v B (insert i S) i ↔ v S < (1 - c i / B) * v (insert i S))) := by sorry

end CompDesign
