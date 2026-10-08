-- Prove2me | Theorems.Thm_DGPNash_WellSupported_lemma4_26_payoff_diff
-- name    : DGPNash.WellSupported.lemma4_26_payoff_diff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:50:11.252621+00:00
-- url     : https://prove2.me/theorems/d4bc74a2-d2e0-48fd-86c9-5144443cea33
-- title:
--   Lemma 4.26 (Lemma 4.29) — expected payoffs are Lipschitz in the opponents' strategies
-- statement:
--   Let $x$ and $y$ be two mixed profiles of a game in normal form with $r\ge2$ players and nonnegative payoffs $u^p_s\ge0$. For a profile $s\in S_{-p}$ of the players other than $p$ write $x_s=\prod_{q\ne p}x^q_{s_q}$ and $y_s=\prod_{q\ne p}y^q_{s_q}$. Then for every player $p$ and every pure strategy $j\in S_p$,
--   $$\Bigl|\sum_{s\in S_{-p}}u^p_{js}\,x_s-\sum_{s\in S_{-p}}u^p_{js}\,y_s\Bigr|\ \le\ \max_{s\in S_{-p}}\{u^p_{js}\}\sum_{q\ne p}\sum_{i\in S_q}\bigl|x^q_i-y^q_i\bigr| .$$
--
--   The expected payoff of a pure strategy thus moves by at most the largest relevant payoff times the total $L_1$ distance between the opponents' mixed strategies. Lemma 4.29 is this inequality for an approximate equilibrium $x$ and its trimmed profile $\hat x$.
--
--   **Formalization Note.** $r\ge2$ and $u\ge0$ are the standing assumptions of Sec. 2.1; nonnegativity is used by the bound. The maximum over $s\in S_{-p}$ is written as a supremum of $u^p$ over full profiles whose $p$-th coordinate is set to $j$, which ranges over the same values. That $x$ and $y$ are mixed profiles is the context of Sec. 4.6 and is stated explicitly. The sum over $q\ne p$ is over the players other than $p$.
-- source:
--   Daskalakis, Goldberg & Papadimitriou, The Complexity of Computing a Nash Equilibrium, SIAM J. Comput. 39(1):195–259 (2009), p. 240, Sec. 4.6, Lemma 4.26; instantiated as Lemma 4.29, p. 244, Sec. 4.7

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_DGPNash_WellSupported_Equilibria

namespace DGPNash.WellSupported

open Finset

/-- **Lemma 4.26 / Lemma 4.29** (Daskalakis–Goldberg–Papadimitriou 2009, p. 240 and p. 244): for
two mixed profiles `x, y` of a game with nonnegative payoffs and at least two players, every player
`p` and every `j ∈ S_p`,
`|Σ_{s ∈ S_{-p}} u^p_{js} x_s − Σ_{s ∈ S_{-p}} u^p_{js} y_s|
  ≤ max_{s ∈ S_{-p}} u^p_{js} · Σ_{q ≠ p} Σ_{i ∈ S_q} |x^q_i − y^q_i|`.
The maximum over `s ∈ S_{-p}` is taken over full profiles `s` with the `p`-th coordinate
overwritten by `j`. -/
theorem lemma4_26_payoff_diff {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (u : ι → (∀ i, S i) → ℝ) (hu : ∀ p s, 0 ≤ u p s) (hr : 2 ≤ Fintype.card ι)
    (x y : ∀ i, S i → ℝ) (hx : AGT.IsMixedProfile x) (hy : AGT.IsMixedProfile y)
    (p : ι) (j : S p) :
    |DGPNash.NashMap.purePayoff u x p j - DGPNash.NashMap.purePayoff u y p j| ≤
      (⨆ s : (∀ i, S i), u p (Function.update s p j)) *
        ∑ q ∈ Finset.univ.erase p, ∑ i : S q, |x q i - y q i| := by sorry

end DGPNash.WellSupported
