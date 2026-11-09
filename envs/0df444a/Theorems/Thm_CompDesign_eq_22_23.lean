-- Prove2me | Theorems.Thm_CompDesign_eq_22_23
-- name    : CompDesign.eq_22_23
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T05:53:07.996036+00:00
-- url     : https://prove2.me/theorems/e21bb3bb-ef01-468b-82c0-9209aec2e046
-- title:
--   (22)–(23) — at an equilibrium, $v(S\cup\{i\})-v(S)\le \frac{x_i}{1-x_i}v(S)$ for $i\notin S$
-- statement:
--   Throughout, $N=\{1,\dots,n\}$ is the set of agents, $B>0$ the budget, $c_i\ge 0$ the private costs, and $v:2^N\to\mathbb R$ a value function satisfying Assumption 3.1: $v(\emptyset)=0$, $v$ monotone ($S\subseteq S'\Rightarrow v(S)\le v(S')$) and submodular ($v(S\cup\{i\})-v(S)\ge v(S'\cup\{i\})-v(S')$ whenever $S\subseteq S'$ and $i\notin S'$). The marginal-contribution payment is $p^{mc}_i(S)=B\,\frac{v(S)-v(S\setminus\{i\})}{v(S)}$ if $i\in S$ and $v(S)>0$, and $0$ otherwise (8); agent $i$'s utility is $u_i(S)=p^{mc}_i(S)-c_i$ if $i\in S$ and $0$ otherwise.
--
--   Assume moreover $c_j<B$ for every agent $j$. Let $S$ be a pure Nash equilibrium of $\Gamma^{mc}$ with $v(S)>0$ and let $i\notin S$. Since $i$ does not prefer to opt in, and $c_i<B$,
--   $$v(S\cup\{i\})\le v(S)\,\frac{B}{B-c_i}\qquad\text{and}\qquad v(S\cup\{i\})-v(S)\le v(S)\,\frac{c_i}{B-c_i}\tag{22}$$
--   and, with $x_i:=c_i/B$,
--   $$v(S\cup\{i\})-v(S)\le \frac{x_i}{1-x_i}\,v(S).\tag{23}$$
--
--   This bounds the relative marginal gain of every absent agent at an equilibrium; summing it over an optimal set gives Theorem 5.1.
--
--   Differences from the source: none.
-- source:
--   Anagnostides, Bhawalkar, Liaw, Mehta, Paes Leme, Teng, Velegkas, Zheng, Compensation Design, arXiv:2607.14438 (version of November 3, 2026, sha256 3d305d4d…), proof of Theorem 5.1, §5.1, eqs. (22)–(23), p.27 (PDF 30)

import Mathlib
import Definitions.Def_CompDesignBFM_IsMonotoneSF
import Definitions.Def_CompDesignBFM_IsSubmodularSF
import Definitions.Def_CompDesignBFM_IsPNE

open CompDesignBFM

namespace CompDesign

/-- Displays (22) and (23), proof of Theorem 5.1, §5.1, p.27 (PDF 30) of Anagnostides et al., *Compensation Design*, arXiv:2607.14438 (version of November 3, 2026, sha256 3d305d4d…).
Let `S` be a pure Nash equilibrium of `Γ^mc` with `v(S) > 0` and `i ∉ S`. Since `i` does not prefer
to opt in and `c_i < B`,
`v(S ∪ {i}) ≤ v(S) B/(B − c_i)` and `v(S ∪ {i}) − v(S) ≤ v(S) c_i/(B − c_i)` (22), and with
`x_i = c_i/B`, `v(S ∪ {i}) − v(S) ≤ x_i/(1 − x_i) · v(S)` (23).

**Formalization Note.** Assumption 3.1, `B > 0`, `c ≥ 0` and `c_i < B` for every agent are binders. -/
theorem eq_22_23 {n : ℕ} (v : Finset (Fin n) → ℝ) (B : ℝ) (c : Fin n → ℝ) (hB : 0 < B)
    (hv0 : v ∅ = 0) (hm : IsMonotoneSF v) (hs : IsSubmodularSF v) (hc : ∀ j, 0 ≤ c j)
    (hcB : ∀ j, c j < B) (S : Finset (Fin n)) (hS : IsPNE v B c S) (hpos : 0 < v S)
    (i : Fin n) (hi : i ∉ S) :
    (v (insert i S) ≤ v S * (B / (B - c i)) ∧ v (insert i S) - v S ≤ v S * (c i / (B - c i))) ∧
    v (insert i S) - v S ≤ (c i / B) / (1 - c i / B) * v S := by sorry

end CompDesign
