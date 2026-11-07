-- Prove2me | Theorems.Thm_DraftPoA_theorem_3_3
-- name    : DraftPoA.theorem_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:39:01.415111+00:00
-- url     : https://prove2.me/theorems/620d351a-ba53-456a-bb20-46afece9907c
-- title:
--   Theorem 3.3: $\mathbb E[\mathrm{SW}]\ge\frac{\lambda}{1+\mu}\bigl(\mathbb E[\mathrm{OPT}]-\frac{2m\delta}{1-\varepsilon}\bigr)$ at Nash, correlated and Bayes–Nash equilibria
-- statement:
--   Let $\rho>1$, $\varepsilon\in(0,1)$, $\tau=\lceil\log_\rho(m/\varepsilon)\rceil$, $\lambda=(1-\varepsilon)/(\tau+1)$ and $\mu=\rho/(\tau+1)$. In every pure or mixed Nash equilibrium, every correlated equilibrium and every Bayes–Nash equilibrium of the draft auction with $m$ items, monotone subadditive bidders and bid increment $\delta\ge0$ (any number of bidders, any priority order, any cap),
--
--   $$\mathbb E[\mathrm{SW}]\ \ge\ \frac{\lambda}{1+\mu}\Bigl(\mathbb E[\mathrm{OPT}]-\frac{2m\delta}{1-\varepsilon}\Bigr).$$
--
--   In particular, with continuous bids ($\delta=0$),
--
--   $$\mathrm{PoA}\ \le\ \frac{1+\mu}{\lambda}=\frac{\lceil\log_\rho(m/\varepsilon)\rceil+1+\rho}{1-\varepsilon}.$$
--
--   This is the finite-$m$ upper bound; Corollary 3.4 chooses $\rho$ and $\varepsilon$ to make it $(1+o(1))\ln m/\ln\ln m$.
--
--   **Formalization Note** The concepts and PoA are those of `DraftPoA.Equilibria`. For $m=0$ Lean's $\log_\rho 0=0$ gives $\tau=0$, and both sides vanish.
--
--   Differences from the source:
--   - reading: expectations under mixed, correlated and Bayes–Nash equilibria (with δ = 0 the strategy space carries no usable σ-algebra) → probability spaces mapping to pure profiles with a measurable outcome map; deviations unrestricted; the inequality in lower-integral form; reason: agrees with the printed inequality whenever the deviation's expectation is defined; the paper asks for measurable strategies so that expectations are defined (p.18)
--   - generalization: in the Bayesian setting the type is the valuation v_i itself, drawn from F_i, and b_i maps types to (pure or mixed) strategies → an arbitrary measurable type space T_i with prior F_i, valuations V_i t measurable in t, and a mixing device (Ω_i, μ_i) with b_i : T_i → Ω_i → Strategy; reason: T_i = the valuations with V_i = id (a one-point device for pure strategies) is the source's setting, so the upper bound specializes to it; the lower bounds are attained at one-point type spaces, where the two coincide
--   - encoding: PoA = sup E[OPT]/E[SW] → a supremum in [0, ∞] with a/0 = ∞ for a > 0 and 0/0 = 0; reason: the paper does not discuss 0/0; all its bounds are at least 1
--   - encoding: m ≥ 1 implicit → every m : ℕ; reason: at m = 0 every welfare is 0 and both claims hold trivially
-- source:
--   Truong, Thach, Chan, Guo, The Price of Anarchy of Draft Auctions, STOC 2027 submission (manuscript sha256 270ffdaa…), Theorem 3.3, p.8 (PDF 9); proofs §3.3, p.8 (PDF 9), and App. A.3, pp.17–18 (PDF 18–19)

import Mathlib
import Definitions.Def_DraftPoA_Equilibria

namespace DraftPoA

/-- Theorem 3.3, p.8 (PDF 9); proofs §3.3, p.8, and App. A.3, pp.17–18 (Truong, Thach, Chan, Guo, *The Price of Anarchy of Draft Auctions*, STOC 2027 submission (manuscript sha256 270ffdaa…)).

Let `ρ > 1`, `ε ∈ (0, 1)`, `τ = ⌈log_ρ(m/ε)⌉`, `λ = (1 − ε)/(τ + 1)` and `μ = ρ/(τ + 1)`. In every
pure or mixed Nash equilibrium, every correlated equilibrium and every Bayes–Nash equilibrium of
the draft auction with `m` items, monotone subadditive bidders and bid increment `δ ≥ 0`,
`E[SW] ≥ (λ/(1 + μ))(E[OPT] − 2mδ/(1 − ε))`. In particular, with `δ = 0`,
`PoA ≤ (1 + μ)/λ = (⌈log_ρ(m/ε)⌉ + 1 + ρ)/(1 − ε)`.

**Formalization Note.** The four concepts are the `Concept`s other than `pureSPE`; the bound
holds over every number of bidders, priority order and cap (`outcomes`). `⌈·⌉₊` is the integer
ceiling of a positive number when `m ≥ 1` (and `0` at `m = 0`, where both sides vanish). -/
theorem theorem_3_3 (m : ℕ) (δ ρ ε : ℝ) (hδ : 0 ≤ δ) (hρ : 1 < ρ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (c : Concept) (hc : c ≠ Concept.pureSPE) :
    let τ : ℕ := ⌈Real.logb ρ ((m : ℝ) / ε)⌉₊
    let lam : ℝ := (1 - ε) / ((τ : ℝ) + 1)
    let mu : ℝ := ρ / ((τ : ℝ) + 1)
    (∀ x ∈ outcomes c ValClass.subadditive m δ,
      lam / (1 + mu) * (x.1 - 2 * (m : ℝ) * δ / (1 - ε)) ≤ x.2) ∧
    poa c ValClass.subadditive m 0 ≤ ENNReal.ofReal ((1 + mu) / lam) ∧
    (1 + mu) / lam = ((τ : ℝ) + 1 + ρ) / (1 - ε) := by sorry

end DraftPoA
