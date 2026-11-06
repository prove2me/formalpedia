-- Prove2me | Theorems.Thm_FirstOrderFG_epoch_base_bound
-- name    : FirstOrderFG.epoch_base_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:56:06.984622+00:00
-- url     : https://prove2.me/theorems/caad00ba-222e-4c38-b825-6a01bbbb7cb8
-- title:
--   Proof of Lemma B.6 — epoch base bound $\le74A\ln(KT)\mathbb E[\bar\rho]+8\sqrt{2A\ln(KT)\mathbb E[\bar\rho]\mathbb E[\sum\ell_{t,k}]}$
-- statement:
--   Throughout, $G=(V,E)$ is a strongly observable directed graph on $K\ge2$ arms ($i\to j$: playing $i$ reveals the loss of $j$), $T\ge3$ is the horizon, and the oblivious adversary fixes losses $\ell_1,\dots,\ell_T\in[0,1]^K$ in advance.
--
--   Suppose $0\in\mathcal B$. For an instance of Algorithm 2 with inputs $A\ge1$, $\theta>0$, started at round $\tau\ge1$ and run on a predictable interval $I$ on which $\mathcal H^{G_{\mathrm{self}}}(q_t)\le A$ (in particular an epoch $\mathcal T_{m,\lambda}$ of Algorithm 4, conditionally on the history before its first round), and every $k\in V_{\mathrm{self}}$,
--   $$
--   \mathbb E_\tau\Big[\sum_{t\in I}\big(\langle q_t,\ell_t\rangle-\ell_{t,k}\big)\Big]\le74A\ln(KT)\,\mathbb E_\tau[\bar\rho_I]+8\sqrt{2A\ln(KT)\,\mathbb E_\tau[\bar\rho_I]\,\mathbb E_\tau\Big[\sum_{t\in I}\ell_{t,k}\Big]} ,
--   $$
--   with $\bar\rho_I=\max_{t\in I}1/x_{t,0}$. At $I=[T]$ this is Eq. (28) of Lemma 4.1.
--
--   Differences from the source:
--   - generalization: an epoch $(m,\lambda)$ of Algorithm 4, conditionally on the history before $t^{\mathrm{start}}_{m,\lambda}$ → any instance of Algorithm 2 on a predictable interval with $\mathcal H^{G_{\mathrm{self}}}(q_t)\le A$; reason: an epoch is such an interval instance (the proof applies Lemma B.1 with $I=\mathcal T_{m,\lambda}$)
--   - encoding: an interval $I$ of rounds, whether $t\in I$ determined before round $t$ is sampled → a continuation predicate on the instance's past arms: round $t\le T$ is in $I$ while it holds; reason: given the history before $\tau$, these are exactly the predictable intervals starting at $\tau$
--   - encoding: conditional expectation $\mathbb E_\tau$ on a filtered probability space → finite sum over the instance's play sequences from round $\tau$ (trajectory law); reason: all randomness is the sequence of played arms; same values
--   - encoding: $\bar\rho_I=\max_{t\in I}1/x_{t,0}$ → $\bar\rho_I=0$ when $I=\emptyset$; reason: the maximum is undefined on $\emptyset$; then every term of the statement is $0$
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, proof of Lemma B.6, pp.33–34 (interval form of Eq. (28), Lemma 4.1, p.11)

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

/-- **The base bound on an epoch (proof of Lemma B.6).** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, proof of Lemma B.6, pp.33–34:
"Since Algorithm 4 ensures `H^{G_self}(q_t) ≤ A` for every `t ∈ T_{m,λ}`, Lemma B.1 applies with
`I = T_{m,λ}`, and the same steps as in the proof of Eq. (28) give
`E_{t^start}[∑_{t ∈ T_{m,λ}} (⟨q_t, ℓ_t⟩ − ℓ_{t,k})] ≤ 74A ln(KT) E_{t^start}[ρ̄_{m,λ}]
+ 8√(2A ln(KT) E_{t^start}[ρ̄_{m,λ}] E_{t^start}[∑_{t ∈ T_{m,λ}} ℓ_{t,k}])`."

This is Eq. (28) of Lemma 4.1 (p.11) for an instance of Algorithm 2 with `0 ∈ B` run on a
predictable interval `I` on which `H^{G_self}(q_t) ≤ A`, for every `k ∈ V_self`; at `I = [T]` it is (28).

**Formalization Note.** Same encoding of the interval and of `E_τ` as in `lemma_B_1`; `ρ̄ = 0` on an
empty interval; `ln = Real.log`. -/
theorem epoch_base_bound {K : ℕ} (T : ℕ) (hK : 2 ≤ K) (hT : 3 ≤ T)
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
    R ≤ 74 * A * Real.log ((K : ℝ) * T) * r
      + 8 * Real.sqrt (2 * A * Real.log ((K : ℝ) * T) * r * L) := by sorry

end FirstOrderFG
