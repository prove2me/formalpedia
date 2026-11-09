-- Prove2me | Theorems.Thm_AutobidSPPE_lemma_2_16
-- name    : AutobidSPPE.lemma_2_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T18:09:32.945762+00:00
-- url     : https://prove2.me/theorems/320936c6-c6c5-44ee-a534-c06e8d0a2503
-- title:
--   Lemma 2.16 — inverse bound for triangular errors
-- statement:
--   Throughout, $n\ge2$ bidders have independent values $v_i\sim\mathrm{Unif}[0,\bar v_i]$ with $0<\bar v_i\le\hat v_i<\infty$ (true supports $\bar v$, certified upper bounds $\hat v$), and budgets $\rho_i>0$; the constants of (10)–(12) are computed from $\hat v$ and $\rho$. For every $y\in\mathcal Y$ and bidder $i$,
--   $$
--   \big\|y_{<i}-p^{[i-1]}(y_i,y_{>i})\big\|_\infty\le C_{\mathrm{tri}}\max_{k<i}|e_k(y)|,\qquad C_{\mathrm{tri}}=(1+L_p)^n, \tag{38}
--   $$
--   an empty maximum being zero. Moreover, with $y^*$ the endpoint equilibrium,
--   $$
--   \|y-y^*\|_\infty\le C_{\mathrm{tri}}\max_i|e_i(y)|\le C_{\mathrm{tri}}W^{n-1}E(y). \tag{39}
--   $$
--
--   **Formalization Note** $y^*$ is any profile that is a conditional equilibrium of the full prefix $[n]$ (unique by Lemma 2.11). The maxima are suprema over index sets, zero over an empty set.
--
--   Differences from the source:
--   - encoding: h_i, e_i, E and p^[k] as functions → defined through a choice among conditional equilibria (condEq); reason: the conditional equilibrium is unique on 𝒴 (Lemma 2.11), so the choice is the paper's map
--   - encoding: the conditional equilibrium p^[k](v) → any full profile z with IsCondEq k z whose later coordinates equal v; reason: such z exists and is unique (Lemma 2.11), so quantifying over all of them states the same fact
--   - encoding: ‖·‖_∞ → the sup norm of Fin n → ℝ (and of functions on index subtypes); reason: Lean's norm on finite products is the maximum norm
--   - encoding: bidders 1, …, n in a fixed order → bidders Fin n in their natural order, paper bidder i = index i − 1; reason: relabeling; every ordering is a relabeling of Fin n, and no instance changes
--   - encoding: max in the response (5)/(7) → sSup of the feasible set; reason: the feasible set is a nonempty bounded closed interval (Lemma 2.7), so its supremum is its maximum
--   - encoding: max_{k<i} |e_k(y)| and max_i |e_i(y)|, an empty maximum being zero → ⨆ over the index subtype {k // k < i} (resp. Fin n); reason: finite index sets, so ⨆ is the maximum; over the empty subtype (i = first bidder) it is 0, as the page prescribes
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), Lemma 2.16, (38)–(39), p.21

import Mathlib
import Definitions.Def_AutobidSPPE_condEq
import Definitions.Def_AutobidSPPE_condError
import Definitions.Def_AutobidSPPE_weightedError
import Definitions.Def_AutobidSPPE_Ctri
import Definitions.Def_AutobidSPPE_W

namespace AutobidSPPE

/-- Lemma 2.16, p.21 (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6)), inverse bound for triangular errors: for every `y ∈ 𝒴` and bidder
`i`, `‖y_{<i} − p^[i−1](yᵢ, y_{>i})‖_∞ ≤ C_tri max_{k<i} |e_k(y)|` (38), an empty maximum being
zero; moreover `‖y − y*‖_∞ ≤ C_tri maxᵢ |eᵢ(y)| ≤ C_tri W^{n−1} E(y)` (39), where `y*` is the
endpoint equilibrium.

**Formalization Note** `p^[i−1](yᵢ, y_{>i})` is `condEq i.val y` (0-based prefix of length
`i.val`); `y*` is any profile with `IsCondEq n` (unique by Lemma 2.11). Maxima over index
subtypes are `⨆`, which is `0` over an empty subtype. -/
theorem lemma_2_16 {n : ℕ} (hn : 2 ≤ n) (vbar vhat ρ : Fin n → ℝ) (hvbar : ∀ i, 0 < vbar i ∧ vbar i ≤ vhat i)
    (hρ : ∀ i, 0 < ρ i) :
    (∀ y ∈ endpointBox vbar ρ, ∀ i : Fin n,
      ‖fun j : {j : Fin n // j < i} => y j - condEq vbar ρ i.val y j‖ ≤
        Ctri vhat ρ * ⨆ k : {k : Fin n // k < i}, |condError vbar ρ k.1 y|) ∧
    (∀ y ∈ endpointBox vbar ρ, ∀ ystar : Fin n → ℝ, IsCondEq vbar ρ n ystar →
      ‖y - ystar‖ ≤ Ctri vhat ρ * ⨆ i, |condError vbar ρ i y| ∧
      Ctri vhat ρ * ⨆ i, |condError vbar ρ i y| ≤
        Ctri vhat ρ * W vhat ρ ^ (n - 1) * weightedError vbar vhat ρ y) := by sorry

end AutobidSPPE
