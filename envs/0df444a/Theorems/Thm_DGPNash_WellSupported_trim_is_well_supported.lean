-- Prove2me | Theorems.Thm_DGPNash_WellSupported_trim_is_well_supported
-- name    : DGPNash.WellSupported.trim_is_well_supported
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:50:26.300777+00:00
-- url     : https://prove2.me/theorems/77e3f3e6-6ae0-465d-b766-e0cc518c5709
-- title:
--   Lemma 4.28 (Lemma 2.1) — trimming an ε-approximate Nash equilibrium gives a √ε(√ε+1+4(r−1)max{u})-well-supported one
-- statement:
--   Let $\mathcal G$ be a game in normal form with $r\ge2$ players, finite strategy sets $S_p$ and nonnegative payoffs $u^p_s\ge0$, and let $\max\{u\}$ be the maximum entry in the payoff tables of $\mathcal G$. Let $\epsilon>0$ and let $x=\{x^p_j\}_{j,p}$ be an $\epsilon$-approximate Nash equilibrium of $\mathcal G$. Put $k=1+1/\sqrt\epsilon$ and let $\hat x$ be the trimmed profile
--   $$\hat x^p_j=\begin{cases}\dfrac{x^p_j}{1-z^p}, & \mathcal U^p_j\ge\mathcal U^p_{\max}-\epsilon k,\\[4pt] 0, & \text{otherwise,}\end{cases}\qquad z^p=\sum_{j\in S_p}x^p_j\,\mathcal X_{\{\mathcal U^p_j<\mathcal U^p_{\max}-\epsilon k\}},$$
--   where $\mathcal U^p_j=\sum_{s\in S_{-p}}u^p_{js}x_s$ and $\mathcal U^p_{\max}=\max_j\mathcal U^p_j$. Then $\hat x$ is a mixed profile and a
--   $$\sqrt\epsilon\cdot\bigl(\sqrt\epsilon+1+4(r-1)\max\{u\}\bigr)$$
--   -approximately well-supported Nash equilibrium of $\mathcal G$: for every player $p$ and all $j,j'\in S_p$, if $\hat{\mathcal U}^p_j>\hat{\mathcal U}^p_{j'}+\sqrt\epsilon(\sqrt\epsilon+1+4(r-1)\max\{u\})$, where $\hat{\mathcal U}$ is computed from $\hat x$, then $\hat x^p_{j'}=0$.
--
--   The lemma reduces the computation of an approximately well-supported equilibrium to that of an approximate one, with a polynomial loss in the accuracy; the converse reduction is immediate since every $\epsilon$-well-supported equilibrium is $\epsilon$-approximate.
--
--   **Formalization Note.** The paper says the well-supported equilibrium "can be computed in polynomial time"; that clause is not formalized. What is stated is that the specific profile $\hat x$ which the proof computes from $x$ has the property. $r$ is the number of players, `Fintype.card ι`, and $r\ge2$ is the standing assumption of Sec. 2.1. $\max\{u\}$ is the maximum over all players and all pure profiles.
-- source:
--   Daskalakis, Goldberg & Papadimitriou, The Complexity of Computing a Nash Equilibrium, SIAM J. Comput. 39(1):195–259 (2009), p. 243, Sec. 4.7, Lemma 4.28 (same statement as Lemma 2.1, p. 199); trimmed profile p. 244, k = 1 + 1/√ε p. 245

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_DGPNash_WellSupported_Equilibria

namespace DGPNash.WellSupported

open Finset

/-- **Lemma 4.28** (= Lemma 2.1) (Daskalakis–Goldberg–Papadimitriou 2009, p. 243 and p. 199): let
`x` be an `ε`-approximate Nash equilibrium, `ε > 0`, of a game with `r ≥ 2` players and
nonnegative payoffs, and let `max{u}` be the largest payoff entry. Then the trimmed profile
`x̂ = trim u x ε k` with `k = 1 + 1/√ε` is a
`√ε · (√ε + 1 + 4(r − 1) max{u})`-approximately well-supported Nash equilibrium (in particular
a mixed profile). -/
theorem trim_is_well_supported {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (u : ι → (∀ i, S i) → ℝ) (hu : ∀ p s, 0 ≤ u p s) (hr : 2 ≤ Fintype.card ι)
    (x : ∀ i, S i → ℝ) (ε : ℝ) (hε : 0 < ε) (hx : IsEpsApproxNash u x ε) :
    IsEpsWellSupportedNash u (trim u x ε (1 + 1 / Real.sqrt ε))
      (Real.sqrt ε * (Real.sqrt ε + 1 + 4 * ((Fintype.card ι : ℝ) - 1) * maxPayoff u)) := by sorry

end DGPNash.WellSupported
