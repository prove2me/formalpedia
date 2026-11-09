-- Prove2me | Theorems.Thm_CompDesign_thm_4_1_potential_increases
-- name    : CompDesign.thm_4_1_potential_increases
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T05:59:36.470843+00:00
-- url     : https://prove2.me/theorems/b776ee4d-760c-418e-bbd8-a58129284801
-- title:
--   Proof of Theorem 4.1 — every strict better response strictly increases $\Phi'$
-- statement:
--   Throughout, $N=\{1,\dots,n\}$ is the set of agents, $B>0$ the budget, $c_i\ge 0$ the private costs, and $v:2^N\to\mathbb R$ a value function satisfying Assumption 3.1: $v(\emptyset)=0$, $v$ monotone ($S\subseteq S'\Rightarrow v(S)\le v(S')$) and submodular ($v(S\cup\{i\})-v(S)\ge v(S'\cup\{i\})-v(S')$ whenever $S\subseteq S'$ and $i\notin S'$). The marginal-contribution payment is $p^{mc}_i(S)=B\,\frac{v(S)-v(S\setminus\{i\})}{v(S)}$ if $i\in S$ and $v(S)>0$, and $0$ otherwise (8); agent $i$'s utility is $u_i(S)=p^{mc}_i(S)-c_i$ if $i\in S$ and $0$ otherwise.
--
--   Assume moreover $c_j<B$ for every agent $j$. Let $\Phi(S)=v(S)\prod_{i\in S}(1-c_i/B)$ and $\Phi'(S)=(\Phi(S),-\sum_{i\in S}c_i)$, ordered lexicographically. If $S'$ is a strict better response from $S$ in $\Gamma^{mc}$ (one agent switches its participation and its utility strictly rises), then
--   $$\Phi'(S)<\Phi'(S').$$
--
--   Opt-ins and opt-outs from positive-value states raise the first coordinate; an opt-out from a zero-value state keeps $\Phi=0$ and raises the second coordinate. Since there are finitely many states, this is what makes every better-response sequence terminate.
--
--   Differences from the source: none.
-- source:
--   Anagnostides, Bhawalkar, Liaw, Mehta, Paes Leme, Teng, Velegkas, Zheng, Compensation Design, arXiv:2607.14438 (version of November 3, 2026, sha256 3d305d4d…), proof of Theorem 4.1, §4.1, p.17 (PDF 20)

import Mathlib
import Definitions.Def_CompDesignBFM_IsMonotoneSF
import Definitions.Def_CompDesignBFM_IsSubmodularSF
import Definitions.Def_CompDesign_IsStrictImprovement
import Definitions.Def_CompDesign_PhiLex

open CompDesignBFM

namespace CompDesign

/-- The lexicographic potential increases, proof of Theorem 4.1, §4.1, p.17 (PDF 20) of Anagnostides et al., *Compensation Design*, arXiv:2607.14438 (version of November 3, 2026, sha256 3d305d4d…):
every strict unilateral improvement `S → S'` of `Γ^mc` strictly increases
`Φ′(S) = (Φ(S), −∑_{i∈S} c_i)` in the lexicographic order, where `Φ(S) = v(S) ∏_{i∈S} (1 − c_i/B)`.

**Formalization Note.** Assumption 3.1, `B > 0`, `c ≥ 0` and Theorem 4.1's `max_i c_i < B` are binders.
The order on `ℝ ×ₗ ℝ` is lexicographic. -/
theorem thm_4_1_potential_increases {n : ℕ} (v : Finset (Fin n) → ℝ) (B : ℝ) (c : Fin n → ℝ)
    (hB : 0 < B) (hv0 : v ∅ = 0) (hm : IsMonotoneSF v) (hs : IsSubmodularSF v)
    (hc : ∀ j, 0 ≤ c j) (hcB : ∀ j, c j < B) (S S' : Finset (Fin n))
    (h : IsStrictImprovement v B c S S') :
    PhiLex v B c S < PhiLex v B c S' := by sorry

end CompDesign
