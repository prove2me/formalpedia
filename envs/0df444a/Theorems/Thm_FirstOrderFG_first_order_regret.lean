-- Prove2me | Theorems.Thm_FirstOrderFG_first_order_regret
-- name    : FirstOrderFG.first_order_regret
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:04:31.9491+00:00
-- url     : https://prove2.me/theorems/36c26b3f-99f2-4ace-a845-cf564025c2d0
-- title:
--   Theorem 4.3 — Algorithm 4 has $\mathrm{Reg}_T=\tilde O(\sqrt{\alpha L^\star}+\alpha)$ on every strongly observable graph
-- statement:
--   Throughout, $G=(V,E)$ is a strongly observable directed graph on $K\ge2$ arms ($i\to j$: playing $i$ reveals the loss of $j$), $T\ge3$ is the horizon, and the oblivious adversary fixes losses $\ell_1,\dots,\ell_T\in[0,1]^K$ in advance.
--
--   There is a universal constant $C>0$ such that for every number of arms $K\ge2$, horizon $T\ge3$, strongly observable directed graph $G$ with independence number $\alpha$, loss sequence $\ell_1,\dots,\ell_T\in[0,1]^K$ chosen by an oblivious adversary, and admissible start rule for the Picard iteration, the expected regret of Algorithm 4 satisfies
--   $$
--   \mathrm{Reg}_T=\mathbb E\Big[\sum_{t=1}^T\ell_{t,I_t}\Big]-L^\star\ \le\ C\Big(\ln^2(KT)\sqrt{\alpha L^\star}+\ln^4(KT)\,\alpha\Big),
--   $$
--   where $L^\star=\min_k\sum_{t=1}^T\ell_{t,k}$. Algorithm 4 receives only $G$, $T$ and the observed feedback; it knows neither $L^\star$ nor $\alpha$.
--
--   This is the first first-order regret bound in terms of the independence number for general strongly observable directed graphs, replacing the clique-partition number of earlier bounds.
--
--   Differences from the source:
--   - reading: $\mathrm{Reg}_T=\tilde O(\sqrt{\alpha L^\star}+\alpha)$ → $\exists C>0$ (before all other quantifiers) with $\mathrm{Reg}_T\le C(\ln^2(KT)\sqrt{\alpha L^\star}+\ln^4(KT)\alpha)$; reason: $\tilde O$ hides factors logarithmic in $K,T$ (footnote 1) and universal constants (p.3); the explicit powers are those the paper's proof yields ($\Gamma_{A^\star}\ln(MT)\le A^\star\cdot3\ln(KT)\cdot\ln^2(KT)$, $A^\star=O(\alpha\ln(KT))$), the strongest reading
--   - reading: Picard iteration in line 6 of Algorithm 2 from an unspecified interior start (\"Fix any $q^{(0)}$\", p.20) → the bound holds for every admissible start rule $q_0(p,\gamma)$; reason: the paper leaves the start free; the statement covers every choice
--   - encoding: expectation over the learner's draws → finite sum over the tree of played arms (trajectory law); reason: all randomness of Algorithm 4 is the sequence of played arms; same values
--   - encoding: horizon $T>2$ → $T\ge3$ ($T\in\mathbb N$); reason: $T$ is an integer; same instances
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Theorem 4.3, Eq. (30), p.12

import Mathlib
import Definitions.Def_FirstOrderFG_StronglyObservable
import Definitions.Def_FirstOrderFG_InteriorStart
import Definitions.Def_FirstOrderFG_Reg
import Definitions.Def_FirstOrderFG_Lstar
import Definitions.Def_FirstOrderFG_indepNumber

namespace FirstOrderFG

/-- **Theorem 4.3: first-order regret on every strongly observable graph.** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, Theorem 4.3,
p.12: "Algorithm 4 (in Appendix B.3) guarantees that `Reg_T = Õ(√(αL⋆) + α)`, (30) for any strongly
observable graph without knowing `L⋆` and `α`."

There is a universal constant `C > 0` such that for every `K ≥ 2` arms, horizon `T ≥ 3`, strongly
observable directed graph `G` on the arms with independence number `α`, oblivious loss sequence
`ℓ₁, …, ℓ_T ∈ [0,1]^K` and admissible Picard start rule, the expected regret of Algorithm 4 satisfies
`Reg_T ≤ C (ln²(KT) √(α L⋆) + ln⁴(KT) α)`.

**Formalization Note.** `Õ(·)` hides factors logarithmic in `K` and `T` (footnote 1, p.1) and `O(·)`
universal constants (p.3); the statement makes them explicit as `C ln²(KT)` and `C ln⁴(KT)`, the
powers the paper's proof yields (`Γ_{A⋆} ln(MT) ≤ A⋆·3ln(KT)·ln²(KT)` with `A⋆ = O(α ln(KT))`, Lemma 2.1,
`J ≤ 3 ln(KT)`, p.30, `M ≤ K`). Algorithm 4 (`Alg4.*`) takes only `G`, `T` and the observed feedback:
`α` and `L⋆` are not inputs. The adversary is oblivious: `ℓ` is fixed before the run. The expectation
is over the finite tree of played arms (`treeExp`). `ln = Real.log`. -/
theorem first_order_regret :
    ∃ C : ℝ, 0 < C ∧ ∀ (K T : ℕ), 2 ≤ K → 3 ≤ T →
      ∀ (E : Fin K → Fin K → Prop) [DecidableRel E], StronglyObservable E →
      ∀ ℓ : ℕ → Fin K → ℝ, (∀ t ∈ Finset.Icc 1 T, ∀ i, ℓ t i ∈ Set.Icc (0 : ℝ) 1) →
      ∀ q₀ : (Fin K → ℝ) → ℝ → Fin K → ℝ, InteriorStart E q₀ →
      Reg E T ℓ q₀ ≤ C * (Real.log ((K : ℝ) * T) ^ 2 * Real.sqrt (indepNumber E * Lstar T ℓ)
        + Real.log ((K : ℝ) * T) ^ 4 * indepNumber E) := by sorry

end FirstOrderFG
