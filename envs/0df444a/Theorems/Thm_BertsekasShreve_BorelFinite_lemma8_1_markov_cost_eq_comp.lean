-- Prove2me | Theorems.Thm_BertsekasShreve_BorelFinite_lemma8_1_markov_cost_eq_comp
-- name    : BertsekasShreve.BorelFinite.lemma8_1_markov_cost_eq_comp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T04:17:11.840947+00:00
-- url     : https://prove2.me/theorems/12e8321f-b209-42f4-ae8a-0af008626293
-- title:
--   Lemma 8.1 — the cost of a Markov policy is the composition of its operators T_μ applied to J₀
-- statement:
--   Consider the finite horizon Borel model of Definition 8.1 and assume (F⁺) or (F⁻). Let $\pi=(\mu_0,\dots,\mu_{N-1})$ be a Markov policy, with $\mu_k\in U(C\mid S)$, and let $J_0:S\to R^*$ be identically zero. Then for $K=1,\dots,N$,
--   $$J_{K,\pi}=(T_{\mu_0}\cdots T_{\mu_{K-1}})(J_0),$$
--   where $T_{\mu_0}\cdots T_{\mu_{K-1}}$ denotes the composition of $T_{\mu_0},\dots,T_{\mu_{K-1}}$.
--
--   The lemma links the integral definition of the cost of a policy to the operator calculus of dynamic programming; it is where assumptions (F⁺)/(F⁻) are needed.
--
--   **Formalization Note** A Markov policy is given as a policy $\pi$ together with kernels $\nu_k\in U(C\mid S)$ such that $\mu_k(\cdot\mid x_0,\dots,x_k)=\nu_k(\cdot\mid x_k)$ for every history. "(F⁺) or (F⁻)" is the hypothesis `FPlus M ∨ FMinus M`.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 194, Lemma 8.1 (Eq. (16) of Chapter 8)

import Mathlib
import Definitions.Def_BertsekasShreve_BorelFinite_Model
import Definitions.Def_BertsekasShreve_BorelFinite_Policy
import Definitions.Def_BertsekasShreve_BorelFinite_Operators

namespace BertsekasShreve.BorelFinite

/-- **Lemma 8.1** (p. 194). Under (F⁺) or (F⁻), for a Markov policy `π = (μ₀, …, μ_{N-1})`
with `μ_k ∈ U(C|S)` and `J₀ ≡ 0`, `J_{K,π} = (T_{μ₀} ⋯ T_{μ_{K-1}})(J₀)` for `K = 1, …, N`. -/
theorem lemma8_1_markov_cost_eq_comp {S C W : Type*}
    [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S] [BertsekasShreve.AnalyticSelection.IsBorelSpace S] [Nonempty S]
    [TopologicalSpace C] [MeasurableSpace C] [BorelSpace C] [BertsekasShreve.AnalyticSelection.IsBorelSpace C] [Nonempty C]
    [TopologicalSpace W] [MeasurableSpace W] [BorelSpace W] [BertsekasShreve.AnalyticSelection.IsBorelSpace W] [Nonempty W]
    (M : Model S C W)
    (hF : FPlus M ∨ FMinus M) (π : Policy M) (ν : Fin M.N → UCS M) (hπ : π.IsMarkovWith ν)
    (K : ℕ) (hK1 : 1 ≤ K) (hKN : K ≤ M.N) :
    J M K π = TmuComp M ν K (J0 S) := by sorry

end BertsekasShreve.BorelFinite
