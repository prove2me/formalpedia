-- Prove2me | Theorems.Thm_DecodablePOMDP_Supplement_theorem_5
-- name    : DecodablePOMDP.Supplement.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:45:28.533063+00:00
-- url     : https://prove2.me/theorems/178f0bb1-4e5f-4075-bfd4-5e79ea317bc1
-- title:
--   Theorem 5 — $\gamma$-$\ell_1$-observable $\Rightarrow$ $(\gamma^2/9)$-decodable; $\alpha$-$\ell_2$-observable $\Rightarrow$ $(\alpha^2/6)$-decodable
-- statement:
--   Let $\mathcal S$ be a finite nonempty state space, $\mathcal O$ a finite observation space, and $K$ an observation channel from $\mathcal S$ to $\mathcal O$ (every $K(\cdot\mid s)$ a probability vector). Let $\alpha,\gamma\in(0,1)$.
--
--   1. If $K$ is $\gamma$-$\ell_1$-observable, then $K$ is $\gamma^2/9$-decodable.
--   2. If $K$ is $\alpha$-$\ell_2$-observable, then $K$ is $\alpha^2/6$-decodable.
--
--   Here $\rho$-decodable means that some decoder $D$ (each $D(\cdot\mid y)$ a probability vector on $\mathcal S$) satisfies
--
--   $$\sum_{y\in\mathcal O}K(y\mid s)\,D(s\mid y)\ \ge\ \rho\qquad\text{for every }s\in\mathcal S.$$
--
--   So decodability is weaker than either observability assumption, and with Theorem 1 constant $\gamma$ or constant $\alpha$ gives quasipolynomial-time planning.
--
--   Differences from the source:
--   - encoding: observation channel K ∈ ℝ^{O×S}, (K)_{y,s} = K(y|s) → `Kc s y = K(y | s)` with every `K(· | s)` a probability vector (`IsDist`), finite types `S`, `O`; reason: the base mission's channel convention; "observation channel" means a stochastic matrix
--   - encoding: state space S (of size S ≥ 1) → `[Nonempty S]`; reason: every state space of the paper is nonempty; with S = ∅ no decoder D(· | y) ∈ Δ(S) exists, so the conclusion is undefined there
--   - encoding: ρ-decodable (Definition 3) → the published `DecodablePOMDP.ChannelDecodable Kc ρ`, which includes ρ ∈ (0, 1]; reason: γ²/9 and α²/6 lie in (0, 1) for α, γ ∈ (0, 1), so the range clause adds nothing
-- source:
--   Dobson, Jog, Shiu, Quasipolynomial-Time Planning for Decodable POMDPs (preprint, sha256 c1256cbe…3584b), Theorem 5, p.13 (proof App. B, pp.21–24)

import Mathlib
import Definitions.Def_CalibratedCE_Forecast_IsDist
import Definitions.Def_DecodablePOMDP_IsDecodable
import Definitions.Def_DecodablePOMDP_Supplement_Observability

namespace DecodablePOMDP.Supplement

open CalibratedCE.Forecast

/-- **Theorem 5 (observability implies decodability).** Let `α, γ ∈ (0, 1)` and let `K` be an
observation channel from a finite nonempty state space `S` to a finite observation space `O`
(each `K(· | s)` a probability vector). If `K` is γ-ℓ1-observable, then `K` is `(γ²/9)`-decodable;
if `K` is α-ℓ2-observable, then `K` is `(α²/6)`-decodable.

Dobson, Jog, Shiu, *Quasipolynomial-Time Planning for Decodable POMDPs* (preprint, sha256
c1256cbe…3584b), Theorem 5, p.13 (proved in App. B, pp.21–24): "Let α, γ ∈ (0, 1). If K ∈ R^{O×S}
is γ-ℓ1-observable, then K is (γ²/9)-decodable. If K is α-ℓ2-observable, then K is
(α²/6)-decodable."

**Formalization Note.**
* `Kc s y = K(y | s)`, the base mission's channel convention; "ρ-decodable" is the published
  `DecodablePOMDP.ChannelDecodable` (Definition 3, p.4).
* `S` is nonempty, as every state space of the paper is (§2, p.5); with `S = ∅` no decoder
  `D(· | y) ∈ Δ(S)` exists while both observability hypotheses hold vacuously.
* The constants are the printed `γ²/9` and `α²/6`. -/
theorem theorem_5 {S O : Type} [Fintype S] [Nonempty S] [Fintype O]
    (Kc : S → O → ℝ) (hK : ∀ s, IsDist (Kc s)) (α γ : ℝ)
    (hα₀ : 0 < α) (hα₁ : α < 1) (hγ₀ : 0 < γ) (hγ₁ : γ < 1) :
    (IsL1Observable Kc γ → ChannelDecodable Kc (γ ^ 2 / 9)) ∧
    (IsL2Observable Kc α → ChannelDecodable Kc (α ^ 2 / 6)) := by sorry

end DecodablePOMDP.Supplement
