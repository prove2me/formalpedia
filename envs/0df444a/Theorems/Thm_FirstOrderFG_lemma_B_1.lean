-- Prove2me | Theorems.Thm_FirstOrderFG_lemma_B_1
-- name    : FirstOrderFG.lemma_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:55:56.870521+00:00
-- url     : https://prove2.me/theorems/ca2378d5-9b04-4bff-9f36-30480372e60c
-- title:
--   Lemma B.1 — base regret on a predictable interval $R_{I,k}\le(56A\ln(sT)+6J)r_I+8\sqrt{2A\ln(sT)r_IL_{I,k}}$
-- statement:
--   Throughout, $G=(V,E)$ is a strongly observable directed graph on $K\ge2$ arms ($i\to j$: playing $i$ reveals the loss of $j$), $T\ge3$ is the horizon, and the oblivious adversary fixes losses $\ell_1,\dots,\ell_T\in[0,1]^K$ in advance.
--
--   Suppose $s=|V_{\mathrm{self}}|>0$ (so $0\in\mathcal B$). Consider an instance of Algorithm 2 with inputs $A\ge1$, $\theta>0$ that starts at round $\tau\ge1$ and runs on an interval $I$ of rounds, membership of round $t$ in $I$ being determined before round $t$ is sampled, and suppose $\mathcal H^{G_{\mathrm{self}}}(q_t)\le A$ for all $t\in I$. Let $\mathbb E_\tau$ be the expectation conditional on the history before $\tau$, $\bar\rho_I=\max_{t\in I}1/x_{t,0}$, $r_I=\mathbb E_\tau[\bar\rho_I]$ and $L_{I,k}=\mathbb E_\tau[\sum_{t\in I}\ell_{t,k}]$. Then for every $k\in V_{\mathrm{self}}$,
--   $$
--   R_{I,k}=\mathbb E_\tau\Big[\sum_{t\in I}\big(\langle q_t,\ell_t\rangle-\ell_{t,k}\big)\Big]\ \le\ (56A\ln(sT)+6J)\,r_I+8\sqrt{2A\ln(sT)\,r_I\,L_{I,k}} ,
--   $$
--   with $J=\lceil\log_2(2MT)\rceil$.
--
--   The bound grows with the expected largest inverse probability of the meta-action, the quantity the master's increasing learning rate is designed to absorb.
--
--   Differences from the source:
--   - encoding: an interval $I$ of rounds, whether $t\in I$ determined before round $t$ is sampled → a continuation predicate on the instance's past arms: round $t\le T$ is in $I$ while it holds; reason: given the history before $\tau$, these are exactly the predictable intervals starting at $\tau$
--   - encoding: conditional expectation $\mathbb E_\tau$ on a filtered probability space → finite sum over the instance's play sequences from round $\tau$ (trajectory law); reason: all randomness is the sequence of played arms; same values
--   - encoding: $\bar\rho_I=\max_{t\in I}1/x_{t,0}$ → $\bar\rho_I=0$ when $I=\emptyset$; reason: the maximum is undefined on $\emptyset$; then every term of the statement is $0$
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Lemma B.1, Eq. (61), p.22

import Mathlib
import Definitions.Def_FirstOrderFG_Alg2_init
import Definitions.Def_FirstOrderFG_Alg2_qOf
import Definitions.Def_FirstOrderFG_StronglyObservable
import Definitions.Def_FirstOrderFG_InteriorStart
import Definitions.Def_FirstOrderFG_Hself
import Definitions.Def_FirstOrderFG_Alg2_InInterval
import Definitions.Def_FirstOrderFG_Alg2_condExp
import Definitions.Def_FirstOrderFG_Alg2_sumOn
import Definitions.Def_FirstOrderFG_Alg2_maxOn
import Definitions.Def_FirstOrderFG_Jconst
import Definitions.Def_FirstOrderFG_Bset
import Definitions.Def_FirstOrderFG_binner
import Definitions.Def_FirstOrderFG_gvec

namespace FirstOrderFG

/-- **Lemma B.1: regret of the self-aware learner on a predictable interval.** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, Lemma B.1,
p.22: "Consider an instance of Algorithm 2 with `0 ∈ B` that starts at round `τ` and runs on an
interval `I` of rounds, where whether `t ∈ I` is determined before round `t` is sampled, and suppose
`H^{G_self}(q_t) ≤ A` for all `t ∈ I`. Denote by `E_τ` the expectation conditional on the history
before `τ`, by `ρ̄_I ≜ max_{t ∈ I} 1/x_{t,0}` the largest inverse probability of meta-action 0, and by
`r_I ≜ E_τ[ρ̄_I]` and `L_{I,k} ≜ E_τ[∑_{t ∈ I} ℓ_{t,k}]`. Then, for every `k ∈ V_self`,
`R_{I,k} ≜ E_τ[∑_{t ∈ I} (⟨q_t, ℓ_t⟩ − ℓ_{t,k})] ≤ (56A ln(sT) + 6J) r_I + 8√(2A ln(sT) r_I L_{I,k})`. (61)"

**Formalization Note.** The instance is `Alg2.init E A θ` started before global round `τ ≥ 1`; the
interval is encoded by a continuation predicate `cont` on the instance's past arms (`Alg2.sumOn`,
`Alg2.maxOn`, `Alg2.InInterval`), and `E_τ` is `Alg2.condExp`. `ρ̄_I = 0` on an empty interval.
`s = |V_self|`, `J = ⌈log₂(2MT)⌉`, `ln = Real.log`. -/
theorem lemma_B_1 {K : ℕ} (T : ℕ) (hK : 2 ≤ K) (hT : 3 ≤ T)
    (E : Fin K → Fin K → Prop) [DecidableRel E] (hSO : StronglyObservable E) (ℓ : ℕ → Fin K → ℝ) (hℓ : ∀ t ∈ Finset.Icc 1 T, ∀ i, ℓ t i ∈ Set.Icc (0 : ℝ) 1)
    (q₀ : (Fin K → ℝ) → ℝ → Fin K → ℝ) (hq₀ : InteriorStart E q₀)
    (hB : (Vself E).Nonempty) (τ : ℕ) (hτ : 1 ≤ τ) (A θ : ℝ) (hA : 1 ≤ A) (hθ : 0 < θ)
    (cont : List (Fin K) → Prop) (hH : ∀ hist, Alg2.InInterval T τ cont hist →
      Hself E T (Alg2.qOf E T q₀ (Alg2.runFrom E T ℓ q₀ τ (Alg2.init E A θ) hist)) ≤ A)
    (k : Fin K) (hk : k ∈ Vself E) :
    let st₀ := Alg2.init E A θ
    let Ex := Alg2.condExp E T ℓ q₀ τ st₀
    let sumI := fun F : ℕ → Alg2.State K → ℝ => Ex (fun h => Alg2.sumOn E T ℓ q₀ cont F τ st₀ [] h)
    let r := Ex (fun h => Alg2.maxOn E T ℓ q₀ cont (fun _ st => 1 / st.x none) τ st₀ [] h)
    let R := sumI (fun t st => ∑ i ∈ Vself E, Alg2.qOf E T q₀ st i * ℓ t i - ℓ t k)
    let L := sumI (fun t _ => ℓ t k)
    let s : ℝ := (Vself E).card
    R ≤ (56 * A * Real.log (s * T) + 6 * (Jconst E T : ℝ)) * r
      + 8 * Real.sqrt (2 * A * Real.log (s * T) * r * L) := by sorry

end FirstOrderFG
