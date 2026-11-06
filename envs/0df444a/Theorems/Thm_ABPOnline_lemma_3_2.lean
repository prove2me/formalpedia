-- Prove2me | Theorems.Thm_ABPOnline_lemma_3_2
-- name    : ABPOnline.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:57:31.911184+00:00
-- url     : https://prove2.me/theorems/0da5c05f-85a9-458b-9c81-8fe02d25e4b6
-- title:
--   Lemma 3.2 — projection of the drift onto the Brownian filtration
-- statement:
--   Let $B$ be a Brownian motion with respect to a filtration $\mathcal G=(\mathcal G_t)_{0\le t\le1}$, and let $a$ be $\mathcal G$-progressively measurable with $\mathbb E\int_0^1a_t^2\,dt<\infty$. Suppose $B_1+\int_0^1a_t\,dt\ge\kappa$ a.s. Let $\mathcal F^B$ be the completed natural filtration of $B$, and let $u$ be an $\mathcal F^B$-progressively measurable version of $u_t=\mathbb E[a_t\mid\mathcal F^B_t]$. Then
--   $$
--   B_1+\int_0^1u_t\,dt=\mathbb E\Big[B_1+\int_0^1a_t\,dt\ \Big|\ \mathcal F^B_1\Big]\ge\kappa\quad\text{a.s.},
--   $$
--   and $\mathbb Eu_t^2\le\mathbb Ea_t^2$ for a.e. $t\in[0,1]$.
--
--   Projecting onto the Brownian filtration preserves the half-line terminal constraint and does not increase the drift budget, which turns Proposition 3.1 into a bound on $E_\star(\kappa)$.
--
--   Differences from the source:
--   - reading: "choose an F^B-progressively measurable version of u_t = E[a_t | F^B_t] for dt ⊗ dP-almost every (t, ω)" → u is a hypothesis: F^B-progressive, with u_t = E[a_t | F^B_t] P-a.s. for a.e. t ∈ [0, 1]; reason: the version is given, as printed; for a.e. t, a.s. is the Fubini form of dt ⊗ dP-a.e. equality for jointly measurable versions
--   - encoding: E ∫₀¹ a²_t dt < ∞; E u²_t, E a²_t → iterated lower integrals in ℝ≥0∞; reason: no junk values
--   - encoding: B a G-Brownian motion with G = (G_t)_{0≤t≤1} → IsBrownianWrt G B P with a filtration indexed by t ≥ 0; reason: only [0, 1] is constrained
-- source:
--   Jo, Lee, The Exact Online Threshold for the Asymmetric Binary Perceptron, arXiv:2609.02124 (artifact sha256 bd5e2bdb18a47b7e806191ae9b888a6e4e7e150a9bd50e541b7587007d07a7a2), Lemma 3.2, (14), p.10 (PDF p.11)

import Mathlib
import Definitions.Def_ABPOnline_IsBrownianWrt
import Definitions.Def_ABPOnline_Estar

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ABPOnline

/-- **Lemma 3.2** (arXiv:2609.02124, printed p.10, PDF p.11). Let `B` be Brownian motion with
respect to a filtration `G`, and let `a` be `G`-progressively measurable with
`E ∫_0^1 a_t² dt < ∞` and `B_1 + ∫_0^1 a_t dt ≥ κ` a.s. Let `F^B` be the completed natural
filtration of `B`, and let `u` be an `F^B`-progressively measurable version of
`u_t = E[a_t | F^B_t]`. Then `B_1 + ∫_0^1 u_t dt = E[B_1 + ∫_0^1 a_t dt | F^B_1] ≥ κ` a.s. (14), and
`E u_t² ≤ E a_t²` for a.e. `t ∈ [0,1]`.

**Formalization Note** "A version for `dt ⊗ dP`-a.e. `(t, ω)`" is read as: for a.e. `t ∈ [0,1]`,
`u_t = E[a_t | F^B_t]` `P`-a.s. The version is a hypothesis, as printed ("choose ... a version").
`E ∫_0^1 a_t² dt` is the iterated lower integral. -/
theorem lemma_3_2 {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (G : Filtration ℝ≥0 mΩ) (B a : ℝ≥0 → Ω → ℝ) (hB : IsBrownianWrt G B P)
    (ha : IsStronglyProgressive G a)
    (ha2 : ∫⁻ ω, (∫⁻ t in Set.Icc (0 : ℝ) 1, ‖a t.toNNReal ω‖ₑ ^ 2) ∂P < ⊤) (κ : ℝ)
    (hterm : ∀ᵐ ω ∂P, κ ≤ ctrlTerminal B a 1 ω) (u : ℝ≥0 → Ω → ℝ)
    (hu : IsStronglyProgressive (brownFiltration P B) u)
    (hver : ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      u t.toNNReal =ᵐ[P] P[a t.toNNReal | brownFiltration P B t.toNNReal]) :
    ctrlTerminal B u 1 =ᵐ[P] P[ctrlTerminal B a 1 | brownFiltration P B 1] ∧
    (∀ᵐ ω ∂P, κ ≤ ctrlTerminal B u 1 ω) ∧
    ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), secondMoment P u t ≤ secondMoment P a t := by sorry

end ABPOnline
