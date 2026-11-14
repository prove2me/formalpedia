-- Prove2me | Theorems.Thm_BilateralProfitLB_theorem_7_1_lower_bound
-- name    : BilateralProfitLB.theorem_7_1_lower_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-13T19:19:16.829189+00:00
-- url     : https://prove2.me/theorems/fe8bd8f6-fe9d-4b40-8cde-cde65a744eb7
-- title:
--   Theorem 7.1 — every algorithm has regret $\Omega(T^{3/5})$ on some independent regular valuations
-- statement:
--   Consider profit maximization in bilateral trade with posted prices in the stochastic setting: the valuation pairs $(s_t,b_t)$ are i.i.d. from a law $\mathcal D$ on $[0,1]^2$, and in round $t$ the learner posts $(p_t,q_t)\in[0,1]^2$ and earns $(q_t-p_t)\mathbb 1\{s_t\le p_t\}\mathbb 1\{q_t\le b_t\}$.
--
--   There are a universal constant $c>0$ and a horizon $T_0$ such that for every $T\ge T_0$ and every learning algorithm $\mathcal A$ (randomized, with feedback the two bits $\mathbb 1\{s_t\le p_t\}$ and $\mathbb 1\{q_t\le b_t\}$ per round, hence in particular with the one trade bit of §2), there is an **independent and regular** distribution $\mathcal D=\mathcal D_s\times\mathcal D_b$, with densities strictly positive on $[0,1]$ and nondecreasing virtual cost and virtual value on $[0,1]$, such that
--   $$R_T(\mathcal A,\mathcal D)=\sup_{(p,q)\in[0,1]^2}\sum_{t=1}^T\mathbb E\big[\mathrm{Profit}_t(p,q)-\mathrm{Profit}_t(p_t,q_t)\big]\ge c\,T^{3/5},$$
--   the expectation being over the valuations and the algorithm's randomness.
--
--   With the $\tilde O(T^{3/5})$ upper bound of Theorem 6.1 this settles the minimax regret rate for independent regular valuations up to logarithmic factors, and separates it from the $\tilde O(\sqrt T)$ rate of the MHR class.
--
--   **Formalization Note** An algorithm is a policy with an arbitrary probability space of seeds, chosen after $T$; the regret bound is witnessed by one comparator $(p,q)\in[0,1]^2$. $T^{3/5}$ is the real power.
--
--   Differences from the source:
--   - generalization: "any learning algorithm" (one-bit feedback, §2) → every randomized two-bit policy; reason: one-bit policies are the two-bit policies whose prices depend only on the trade bits, and the proof is for this class ("an even stronger class of algorithms", p.49)
--   - reading: "for any learning algorithm $\mathcal A$ there exists $\mathcal D$ … $\ge cT^{3/5}$ for some universal $c$ and $T$ large enough" → $\exists c>0,\exists T_0,\forall T\ge T_0,\forall\mathcal A,\exists\mathcal D$; reason: §2 (p.4) defines the minimax regret as the infimum over algorithms of the worst case over instances, Table 1 lists $\tilde\Theta(T^{3/5})$ (Thms. 6.1 & 7.1) as a minimax rate, and the proof's instance depends on $T$ through $K=\lceil T^{1/5}\rceil$
--   - encoding: $\Omega(T^{3/5})$ "for $T$ large enough" and $\sup_{(p,q)}$ → $\exists c>0$, $\exists T_0$, and one comparator in $[0,1]^2$ achieving the bound; reason: the supremum is attained (p.4)
--   - encoding: "regular and independent distributions" → an independent environment with supports $[0,1]$, densities strictly positive on $[0,1]$, and Definition 2.2 for seller and buyer; reason: the standing assumption of §2 (p.4) for this class; requiring it of the hard instance makes the bound stronger
-- source:
--   Brüstle, di Gregorio, Fusco, Leonardi, Regret Bounds for Profit Maximization in Bilateral Trade: Learning the Best Posted-Price Mechanism (manuscript, STOC 2027 submission, sha256 e91e81279505b765c7c96c219d674c0fbbbd6ca47a00da8fe228d498ca25ac87), Theorem 7.1, p.49 (PDF 51), proof pp.49–53 (PDF 51–55); model §2, pp.3–4 (PDF 5–6)

import Mathlib
import Definitions.Def_BilateralProfitLB_Stochastic

namespace BilateralProfitLB

open MeasureTheory MechanismDesign.BilateralTrade

/-- **Theorem 7.1**, Brüstle, di Gregorio, Fusco, Leonardi (manuscript, sha256 e91e8127…), p.49
(PDF 51): for any learning algorithm `𝒜` there exist regular and independent distributions `𝒟`
such that `𝒜` suffers regret `R_T(𝒜, 𝒟) ≥ c T^{3/5}`, for some universal constant `c` and `T`
large enough.

Stated as: there are `c > 0` and `T₀` such that for every horizon `T ≥ T₀`, every probability
space `(Ω, P)` of seeds and every randomized two-bit posted-price policy `π` on it, there is an
independent environment `E` (seller and buyer independent, densities strictly positive on
`[0, 1]`) with both virtual-value functions nondecreasing on `[0, 1]` (Definition 2.2) and a
comparator `(p, q) ∈ [0, 1]²` with
`Σ_{t < T} (E[Profit_t(p, q)] − E[Profit_t(p_t, q_t)]) ≥ c T^{3/5}`, the valuations being
i.i.d. with law `E.prior` and independent of the seed.

**Formalization Note.** Two-bit policies (feedback `(1{s_t ≤ p_t}, 1{q_t ≤ b_t})`) contain the
paper's one-bit algorithms (`Policy.OneBit`); the proof is for this class (p.49). `c` and `T₀`
come first; `𝒟` may depend on `T` and on the algorithm (the minimax reading, §2 p.4 and
Table 1). `R_T ≥ c T^{3/5}` is witnessed by one comparator (the supremum of §2 is attained).
`T^{3/5}` is the real power `(T : ℝ) ^ (3/5 : ℝ)`. -/
theorem theorem_7_1_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∃ T₀ : ℕ, ∀ T : ℕ, T₀ ≤ T →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (π : Policy Ω),
        ∃ E : Environment, UnitSupport E ∧ E.Regular ∧
          ∃ a ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1,
            c * (T : ℝ) ^ ((3 : ℝ) / 5) ≤ regret π P E.prior T a := by sorry

end BilateralProfitLB
