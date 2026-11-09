-- Prove2me | Theorems.Thm_CompDesign_thm_4_1_opt_out_iff
-- name    : CompDesign.thm_4_1_opt_out_iff
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T05:56:15.072627+00:00
-- url     : https://prove2.me/theorems/0e04be1b-f607-4c19-9236-5d28b5398b09
-- title:
--   Proof of Theorem 4.1 — strictly profitable opt-out $\iff v(S_{-i})>(1-c_i/B)\,v(S)$
-- statement:
--   Throughout, $N=\{1,\dots,n\}$ is the set of agents, $B>0$ the budget, $c_i\ge 0$ the private costs, and $v:2^N\to\mathbb R$ a value function satisfying Assumption 3.1: $v(\emptyset)=0$, $v$ monotone ($S\subseteq S'\Rightarrow v(S)\le v(S')$) and submodular ($v(S\cup\{i\})-v(S)\ge v(S'\cup\{i\})-v(S')$ whenever $S\subseteq S'$ and $i\notin S'$). The marginal-contribution payment is $p^{mc}_i(S)=B\,\frac{v(S)-v(S\setminus\{i\})}{v(S)}$ if $i\in S$ and $v(S)>0$, and $0$ otherwise (8); agent $i$'s utility is $u_i(S)=p^{mc}_i(S)-c_i$ if $i\in S$ and $0$ otherwise.
--
--   Assume moreover $c_j<B$ for every agent $j$. Let $i\in S$, write $S_{-i}=S\setminus\{i\}$, and suppose $v(S)>0$. Then opting out is strictly profitable, $u_i(S_{-i})>u_i(S)$, if and only if $p^{mc}_i(S)<c_i$, and
--   $$B\,\frac{v(S)-v(S_{-i})}{v(S)}<c_i \iff v(S_{-i})>\Big(1-\frac{c_i}{B}\Big)v(S).$$
--
--   This is the opt-out case, from a positive-value state, of the potential argument for Theorem 4.1.
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

/-- Opt-out equivalence, proof of Theorem 4.1, §4.1, p.17 (PDF 20) of Anagnostides et al., *Compensation Design*, arXiv:2607.14438 (version of November 3, 2026, sha256 3d305d4d…).
For an agent `i ∈ S` with `v(S) > 0`, opting out is strictly profitable iff
`B (v(S) − v(S₋ᵢ))/v(S) < c_i`, iff `v(S₋ᵢ) > (1 − c_i/B) v(S)`, where `S₋ᵢ = S ∖ {i}`.

**Formalization Note.** The standing assumptions (Assumption 3.1, `B > 0`, `c ≥ 0`) and the hypothesis
`max_i c_i < B` of Theorem 4.1 are kept as binders. -/
theorem thm_4_1_opt_out_iff {n : ℕ} (v : Finset (Fin n) → ℝ) (B : ℝ) (c : Fin n → ℝ) (hB : 0 < B)
    (hv0 : v ∅ = 0) (hm : IsMonotoneSF v) (hs : IsSubmodularSF v) (hc : ∀ j, 0 ≤ c j)
    (hcB : ∀ j, c j < B) (S : Finset (Fin n)) (i : Fin n) (hi : i ∈ S) (hpos : 0 < v S) :
    (util v B c S i < util v B c (S.erase i) i ↔ mcPay v B S i < c i) ∧
    (mcPay v B S i < c i ↔ (1 - c i / B) * v S < v (S.erase i)) := by sorry

end CompDesign
