-- Prove2me | Theorems.Thm_AutobidSPPE_lemma_2_11
-- name    : AutobidSPPE.lemma_2_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T18:03:35.393621+00:00
-- url     : https://prove2.me/theorems/ca3364f7-7f20-4817-afe3-cffe4185e59a
-- title:
--   Lemma 2.11 — unique and Lipschitz conditional equilibria
-- statement:
--   Throughout, $n\ge2$ bidders have independent values $v_i\sim\mathrm{Unif}[0,\bar v_i]$ with $0<\bar v_i$, and budgets $\rho_i>0$. Fix the bidder order.
--
--   1. For each $k=1,\dots,n$ and later endpoints $v\in\mathcal Y_{>k}=\prod_{j>k}[\underline y_j,\bar v_j]$ there is a unique conditional equilibrium $p^{[k]}(v)\in\mathcal Y_{\le k}$ of bidders $1,\dots,k$ (the prefix plays capped endpoint responses, the later endpoints are fixed at $v$).
--   2. Each map $v\mapsto p^{[k]}(v)$ is Lipschitz on its parameter rectangle (maximum norms).
--   3. The full Bayesian SPPE is unique.
--
--   In particular the targets $h_i(v)=p^{[i]}_i(v)$ are well defined.
--
--   **Formalization Note** A conditional equilibrium is a full profile $z$ (prefix and fixed suffix) with $z\in\mathcal Y$ and $z_i=\mathsf b_i(z_{-i})$ for $i\le k$. Lipschitz continuity is stated as: there is $L$ with $\|z_{\le k}-z'_{\le k}\|_\infty\le L\|z_{>k}-z'_{>k}\|_\infty$ for any two conditional equilibria $z,z'$ of the prefix.
--
--   Differences from the source:
--   - encoding: the conditional equilibrium p^[k](v) → any full profile z with IsCondEq k z whose later coordinates equal v; reason: such z exists and is unique (Lemma 2.11), so quantifying over all of them states the same fact
--   - encoding: the prefix maps are Lipschitz on their parameter rectangles → ∃ L such that any two conditional equilibria of the prefix satisfy ‖prefix difference‖ ≤ L·‖suffix difference‖; reason: the Lipschitz property of the unique conditional-equilibrium map, stated through the profiles it produces
--   - encoding: ‖·‖_∞ → the sup norm of Fin n → ℝ (and of functions on index subtypes); reason: Lean's norm on finite products is the maximum norm
--   - encoding: bidders 1, …, n in a fixed order → bidders Fin n in their natural order, paper bidder i = index i − 1; reason: relabeling; every ordering is a relabeling of Fin n, and no instance changes
--   - generalization: a fixed tie-breaking rule → every deterministic single-winner tie rule (universally quantified); reason: the statement for every rule specializes to the paper's fixed rule
--   - reading: x_i(α) := 1{α_i v_i ≥ max_j α_j v_j} using a fixed tie-breaking rule (Problem 1.1) → x_i = 1 iff bidder i is the one bidder the tie rule picks among the highest bids; reason: under the literal ≥ every tied bidder wins and the all-zero profile is a second SPPE, contradicting the uniqueness the paper proves; §2.2 ('An arbitrary fixed tie rule is used … zero-bid ties pay zero') fixes the single-winner reading
--   - encoding: max in the response (5)/(7) → sSup of the feasible set; reason: the feasible set is a nonempty bounded closed interval (Lemma 2.7), so its supremum is its maximum
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), Lemma 2.11, p.17

import Mathlib
import Definitions.Def_AutobidSPPE_IsCondEq
import Definitions.Def_AutobidSPPE_IsBayesianSPPE
import Definitions.Def_AutobidSPPE_endpointFloor

namespace AutobidSPPE

/-- Lemma 2.11, p.17 (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6)): for each `k = 1, …, n` and later endpoints `v ∈ 𝒴_{>k}` there is a
unique conditional equilibrium `p^[k](v) ∈ 𝒴_{≤k}` of bidders `1, …, k`; these maps are Lipschitz
on their parameter rectangles; and the full Bayesian SPPE is unique.

**Formalization Note** Bidders `1, …, k` are the indices `j` with `j.val < k`; the later
endpoints are those with `k ≤ j.val`. A conditional equilibrium is a full profile `z` with
`IsCondEq k z`. Lipschitz continuity is stated between any two conditional equilibria of the same
prefix, in sup norms (the sup norm over an empty index type is `0`). -/
theorem lemma_2_11 {n : ℕ} (hn : 2 ≤ n) (vbar ρ : Fin n → ℝ) (hvbar : ∀ i, 0 < vbar i) (hρ : ∀ i, 0 < ρ i)
    (tie : TieRule n) :
    (∀ k : ℕ, 1 ≤ k → k ≤ n → ∀ v : Fin n → ℝ,
      (∀ j : Fin n, k ≤ j.val → endpointFloor vbar ρ j ≤ v j ∧ v j ≤ vbar j) →
      ∃! z : Fin n → ℝ, IsCondEq vbar ρ k z ∧ ∀ j : Fin n, k ≤ j.val → z j = v j) ∧
    (∀ k : ℕ, 1 ≤ k → k ≤ n → ∃ L : ℝ, ∀ y z : Fin n → ℝ,
      IsCondEq vbar ρ k y → IsCondEq vbar ρ k z →
      ‖fun j : {j : Fin n // j.val < k} => y j - z j‖ ≤
        L * ‖fun j : {j : Fin n // k ≤ j.val} => y j - z j‖) ∧
    (∀ α β : Fin n → ℝ, IsBayesianSPPE vbar ρ tie α → IsBayesianSPPE vbar ρ tie β → α = β) := by sorry

end AutobidSPPE
