-- Prove2me | Theorems.Thm_CodeSW_lemma_9
-- name    : CodeSW.lemma_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:28:50.669112+00:00
-- url     : https://prove2.me/theorems/78c03d55-c565-4712-838c-67a99c746db8
-- title:
--   Lemma 9 — SW is faster than Metropolis: $\tau(P_{\mathrm{Metropolis}})\ge\frac12\tau(P_{\mathrm{SW}})$
-- statement:
--   **The Swendsen-Wang dynamics of the random cluster model is faster than Metropolis dynamics, up to a constant.** Let $0<p<1$, let $\phi$ be the random cluster model, and write $d_{\mathrm{Met}},d_{\mathrm{SW}}$ for the worst-case total variation distances to $\phi$ of the lazy Metropolis chain and of $P_{\mathrm{SW}}$. For every $t\ge0$,
--   $$d_{\mathrm{Met}}(t)\le\frac1{2e}\ \Longrightarrow\ d_{\mathrm{SW}}(2t)\le\frac1{2e}.$$
--   Equivalently,
--   $$\tau(P_{\mathrm{Metropolis}})\ge\frac12\tau(P_{\mathrm{SW}}).$$
--
--   This transfers the rapid mixing of a local chain, which is analysed by flows, to the global chain.
--
--   Differences from the source:
--   - encoding: τ(P_Metropolis) ≥ ½τ(P_SW), for τ = min_t[max_x ∑_y |P^t(x,y) − ϕ(y)| ≤ e^{−1}] → for every t, distStationary (metropolis) ϕ t ≤ 1/(2e) implies distStationary (swRC) ϕ (2t) ≤ 1/(2e); reason: total variation is half the ℓ¹ distance and d(t) is non-increasing, so the two forms are equivalent
-- source:
--   Hangleiter, Ju, Vazirani, Code Swendsen-Wang Dynamics, arXiv:2510.08446 (manuscript sha256 4e4abb5e…), Lemma 9, p.18

import Definitions.Def_CodeSW_metropolis
import Definitions.Def_mm_mixing
open Matrix

namespace CodeSW

/-- **Lemma 9 (SW is faster than Metropolis dynamics).** The SW dynamics of the RC model is faster
than Metropolis dynamics (up to a constant): `τ(P_Metropolis) ≥ ½ τ(P_SW)`. Equivalently, for
`0 < p < 1` and every `t`, if the lazy single-check Metropolis chain is within total variation
`1/(2e)` of `ϕ` after `t` steps, then the SW chain of the RC model is within `1/(2e)` of `ϕ` after
`2t` steps (Hangleiter, Ju, Vazirani, *Code Swendsen-Wang Dynamics*, arXiv:2510.08446, manuscript
sha256 4e4abb5e…, Lemma 9, p.18).

**Formalization Note** `τ` is the p.13 mixing time (`ℓ¹` threshold `e^{−1}`, total variation
`1/(2e)`). The implication for every `t` is equivalent to `τ(P_SW) ≤ 2τ(P_Metropolis)` because
`d(t)` is non-increasing. -/
theorem lemma_9 {c n : ℕ} (h : Matrix (Fin c) (Fin n) (ZMod 2)) (p : ℝ) (hp0 : 0 < p)
    (hp1 : p < 1) (t : ℕ)
    (ht : MarkovMixing.distStationary (metropolis h p) (rc h p) t ≤ 1 / (2 * Real.exp 1)) :
    MarkovMixing.distStationary (swRC h p) (rc h p) (2 * t) ≤ 1 / (2 * Real.exp 1) := by sorry

end CodeSW
