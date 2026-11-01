-- Prove2me | Theorems.Thm_ConstrainedTrading_theorem_3_1_problemEA_integral_optimum
-- name    : ConstrainedTrading.theorem_3_1_problemEA_integral_optimum
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:21:23.667761+00:00
-- url     : https://prove2.me/theorems/4a598353-740e-4067-9a02-d7932b75cc58
-- title:
--   Theorem 3.1 — Problem EA has an integral optimum
-- statement:
--   Let $(N,E)$ be a finite trading network, arc $e$ being a trade sold by $e^+$ and bought by $e^-$. Suppose every agent's valuation is separable, $w_i(y^i)=w_i^+(y^{i+})+w_i^-(y^{i-})$, where $w_i^+:\mathbb Z^{\delta^+(i)}\to\mathbb R\cup\{-\infty\}$ is M$^\sharp$-concave on the outgoing arcs and $w_i^-(y)=\sum_{e\in\delta^-(i)}c_e y_e$ is linear on the incoming arcs. Let $P=P(\rho)$ be a nonempty integral polymatroid. Then the relaxed efficient-allocation problem
--   $$
--   \max_{x\in P}\ \sum_{i\in N}\Bigl[\hat w_i^+\bigl(x|_{\delta^+(i)}\bigr)+\hat w_i^-\bigl(-x|_{\delta^-(i)}\bigr)\Bigr]
--   $$
--   attains its maximum at an integral outcome $z\in\mathbb Z^E\cap P$.
--
--   This is the paper's main positive result: in two-sided (separable) markets an integral polymatroid constraint on trades preserves the integrality of the efficient-allocation relaxation, which the paper connects to the existence of competitive equilibria; §4 shows that it fails for multi-sided markets.
--
--   **Formalization Note** The objective is `eaObjective`, with constraint (5) built in and values in `EReal`.
--
--   Differences from the source:
--
--   - reading: Problem EA (3)–(5): max Σᵢ (w⁺ᵢ(y^{i+}) + w⁻ᵢ(y^{i−})) s.t. x ∈ P, (5) → maximize Σᵢ [ŵ⁺ᵢ(x|δ⁺(i)) + ŵ⁻ᵢ(−x|δ⁻(i))] over real x ∈ P; reason: read as an integer program 'has an integral optimum' would be empty; §3's setup (p.7) and Lemma 3.1 maximize the concave extensions over x ∈ P
--   - reading: Problem EA has an integral optimum → ∃ integer z ∈ P with objective(x) ≤ objective(z) for every x ∈ P; reason: the conclusion asserts both attainment of the maximum and integrality; under R1 P is a polytope and both hold
--   - generalization: each arc is a trade between two agents (p.2–3: 'any arc e between agents i and j') → arbitrary seller and buyer maps E → N, loops allowed (a loop's x_e enters both w⁺ and w⁻ of its agent); reason: for loopless networks the statement is exactly the source's; loops only add instances
--   - encoding: net flows yⁱ subject to (5) yⁱₑ = xₑ = −yʲₑ → y^{i+} = x|δ⁺(i), y^{i−} = −x|δ⁻(i) parametrized by x; one coefficient vector c : E → ℝ for all linear w⁻ᵢ; reason: (5) is solved for the net flows; each arc has one buyer, so c encodes every w⁻ᵢ; same instances
--   - reading: w linear → w(y) = Σ_e c_e y_e with a coefficient vector c (no constant term); reason: the strict sense of 'linear'
--   - reading: integral polymatroid P_f = {x ∈ ℝ^E : Σ_{e∈S} x_e ≤ f(S) ∀S ⊆ E} (p.4, no sign constraint) → P(ρ) = {x : x ≥ 0, Σ_{e∈S} x_e ≤ ρ(S) ∀S}; reason: standard meaning of polymatroid, outcomes are x ∈ ℤ₊^E (p.3); without x ≥ 0 the statement is false (E = {e}, ρ ≡ 0, seller valuation w(z) = −z: the objective −x is unbounded on (−∞, 0])
--   - reading: concave extension f̂(x) = max{Σ_z λ_z f(z) : Σ_z λ_z z = x, 0 ≤ λ_z ≤ 1, Σ_z λ_z = 1} (Defs 2.8–2.9, p.5) → f̂(x) = sSup over finite convex representations in EReal, sup ∅ = −∞; reason: a max need not be attained for a general f; the sup is the total version, and it is the convex-combination hull, not the closed concave closure
--   - encoding: an integral polymatroid P → hypothesis P(ρ) nonempty; reason: nondegeneracy: it only excludes P = ∅ (some ρ(S) < 0), where there is no feasible point to exhibit; when P ≠ ∅, 0 ∈ P
--   - reading: M♯-concave f : ℤ^E → R, exchange 'for all x, y ∈ B' with B unnamed (Def 2.7, p.4; p.5) → f : ℤ^E → ℝ ∪ {−∞}, exchange for x, y ∈ dom f = {z : f z ≠ −∞}; reason: the paper's valuations take values in ℝ ∪ {−∞} (p.3, footnote 3) and p.5 defines dom f; the real-valued case is dom f = ℤ^E
-- source:
--   Kizilkale, Vohra, Constrained Trading Networks, arXiv:2008.09757v1, Theorem 3.1, p.8; Problem EA (3)–(5), p.8

import Mathlib
import Definitions.Def_ConstrainedTrading_MNatConcave
import Definitions.Def_SteinitzExchange_Duality_SetFunction
import Definitions.Def_ConstrainedTrading_polymatroid
import Definitions.Def_ConstrainedTrading_eaObjective

namespace ConstrainedTrading

/-- **Theorem 3.1** (Kizilkale–Vohra, *Constrained Trading Networks*, arXiv:2008.09757v1, p.8):
"Problem EA has an integral optimum." Let `(N, E)` be a finite trading network (arc `e` sold by
`seller e`, bought by `buyer e`), let every agent's valuation be separable,
`wᵢ(yⁱ) = w⁺ᵢ(y^{i+}) + w⁻ᵢ(y^{i−})`, with `w⁺ᵢ` M♯-concave on its outgoing arcs and
`w⁻ᵢ(y) = Σ_{e∈δ⁻(i)} c_e y_e` linear on its incoming arcs, and let `P = P(ρ)` be a nonempty
integral polymatroid. Then the relaxed Problem EA, maximize
`Σᵢ [ŵ⁺ᵢ(x|_{δ⁺(i)}) + ŵ⁻ᵢ(−x|_{δ⁻(i)})]` over `x ∈ P`, attains its maximum at an integral
outcome `z ∈ ℤ^E ∩ P`.

**Formalization Note** The objective is `eaObjective` (constraint (5) built in, values in
`EReal`, reading R2: the concave-extension relaxation over real `x`). The conclusion asserts
attainment and integrality together. Any finite `N` and `E`, any seller/buyer maps (loops
allowed), any M♯-concave `w⁺ᵢ` (no nonemptiness of the domain), any `c`, and any integer
submodular `ρ` (not necessarily monotone or normalized) are allowed; `P(ρ)` includes `x ≥ 0`
(reading R1). Nonemptiness of `P` excludes only the case with no feasible outcome. -/
theorem theorem_3_1_problemEA_integral_optimum {N E : Type*} [Fintype N] [Fintype E]
    [DecidableEq N] [DecidableEq E] (seller buyer : E → N)
    (wPlus : (i : N) → ({e // seller e = i} → ℤ) → WithBot ℝ) (hw : ∀ i, MNatConcave (wPlus i))
    (c : E → ℝ) (ρ : Finset E → ℤ) (hρ : SteinitzExchange.Duality.IsSubmodular ρ) (hP : (polymatroid ρ).Nonempty) :
    ∃ z : E → ℤ, (fun e => (z e : ℝ)) ∈ polymatroid ρ ∧
      ∀ x ∈ polymatroid ρ,
        eaObjective seller buyer wPlus c x ≤
          eaObjective seller buyer wPlus c (fun e => (z e : ℝ)) := by sorry

end ConstrainedTrading
