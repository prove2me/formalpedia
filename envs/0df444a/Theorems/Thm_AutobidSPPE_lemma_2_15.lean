-- Prove2me | Theorems.Thm_AutobidSPPE_lemma_2_15
-- name    : AutobidSPPE.lemma_2_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T18:03:52.394637+00:00
-- url     : https://prove2.me/theorems/404ad935-c276-4d5b-9d49-00064c7fb248
-- title:
--   Lemma 2.15 — reduced scalar sector, including boundary targets
-- statement:
--   Throughout, $n\ge2$ bidders have independent values $v_i\sim\mathrm{Unif}[0,\bar v_i]$ with $0<\bar v_i\le\hat v_i<\infty$ (true supports $\bar v$, certified upper bounds $\hat v$), and budgets $\rho_i>0$; the constants of (10)–(12) are computed from $\hat v$ and $\rho$. Fix a bidder $i$ and later endpoints $v\in\prod_{j>i}[\underline y_j,\bar v_j]$, and write
--   $$
--   h_i(v)=p^{[i]}_i(v),\qquad q_i(t,v)=t-\mathsf b_i\big(p^{[i-1]}(t,v),v\big),\qquad t\in[\underline y_i,\bar v_i].
--   $$
--   (For $i=1$ the prefix is empty; for $i=n$ the suffix is empty.) Then $q_i(h_i(v),v)=0$ and, with $a=\underline\gamma$,
--   $$
--   a\ \le\ \frac{q_i(t,v)}{t-h_i(v)}\ \le\ b_0\qquad\text{whenever } t\ne h_i(v). \tag{34}
--   $$
--
--   **Formalization Note** $h_i(v)$ is coordinate $i$ of a conditional equilibrium of the prefix $[i]$ with suffix $v$, and $p^{[i-1]}(t,v)$ is the prefix of a conditional equilibrium of $[i-1]$ whose own coordinate is $t$ and whose suffix is $v$; membership in $\mathcal Y$ gives $t\in[\underline y_i,\bar v_i]$.
--
--   Differences from the source:
--   - encoding: the conditional equilibrium p^[k](v) → any full profile z with IsCondEq k z whose later coordinates equal v; reason: such z exists and is unique (Lemma 2.11), so quantifying over all of them states the same fact
--   - encoding: bidders 1, …, n in a fixed order → bidders Fin n in their natural order, paper bidder i = index i − 1; reason: relabeling; every ordering is a relabeling of Fin n, and no instance changes
--   - encoding: max in the response (5)/(7) → sSup of the feasible set; reason: the feasible set is a nonempty bounded closed interval (Lemma 2.7), so its supremum is its maximum
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), Lemma 2.15, (34), p.20

import Mathlib
import Definitions.Def_AutobidSPPE_IsCondEq
import Definitions.Def_AutobidSPPE_gammaLow
import Definitions.Def_AutobidSPPE_b0

namespace AutobidSPPE

/-- Lemma 2.15, p.20 (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6)), the reduced scalar sector: fix bidder `i` and later endpoints
`v ∈ ∏_{j>i}[y̲ⱼ, v̄ⱼ]`, let `hᵢ(v) = p^[i]ᵢ(v)` and
`qᵢ(t, v) = t − 𝖻ᵢ(p^[i−1](t, v), v)` for `t ∈ [y̲ᵢ, v̄ᵢ]`. Then `qᵢ(hᵢ(v), v) = 0` and
`a ≤ qᵢ(t, v)/(t − hᵢ(v)) ≤ b₀` whenever `t ≠ hᵢ(v)` (34), with `a = γ̲`.

**Formalization Note** `yh` is the conditional equilibrium of the prefix `[i]` (indices
`≤ i`, `IsCondEq (i.val + 1)`) with suffix `v`, so `hᵢ(v) = yh i`; `yt` is the conditional
equilibrium of the prefix `[i − 1]` (`IsCondEq i.val`) with own endpoint `yt i = t` and the same
suffix, so `qᵢ(t, v) = yt i − 𝖻ᵢ(yt)`. Membership of `yt` in `𝒴` gives `t ∈ [y̲ᵢ, v̄ᵢ]`. For
`i.val = 0` the prefix is empty; for `i.val = n − 1` the suffix is empty. -/
theorem lemma_2_15 {n : ℕ} (hn : 2 ≤ n) (vbar vhat ρ : Fin n → ℝ) (hvbar : ∀ i, 0 < vbar i ∧ vbar i ≤ vhat i)
    (hρ : ∀ i, 0 < ρ i) :
    ∀ (i : Fin n) (yh : Fin n → ℝ), IsCondEq vbar ρ (i.val + 1) yh →
      ∀ yt : Fin n → ℝ, IsCondEq vbar ρ i.val yt → (∀ j : Fin n, i < j → yt j = yh j) →
        (yt i = yh i → yt i - endpointResponse vbar ρ yt i = 0) ∧
        (yt i ≠ yh i →
          gammaLow vhat ρ ≤ (yt i - endpointResponse vbar ρ yt i) / (yt i - yh i) ∧
          (yt i - endpointResponse vbar ρ yt i) / (yt i - yh i) ≤ b0 vhat ρ) := by sorry

end AutobidSPPE
