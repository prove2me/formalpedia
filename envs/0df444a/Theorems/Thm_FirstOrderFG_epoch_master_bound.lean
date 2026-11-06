-- Prove2me | Theorems.Thm_FirstOrderFG_epoch_master_bound
-- name    : FirstOrderFG.epoch_master_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:57:44.697487+00:00
-- url     : https://prove2.me/theorems/64332594-f103-48cc-a151-3751d08957b5
-- title:
--   Proof of Lemma B.6 — epoch master bound $\le9\ln(MT)/\theta+12\theta\mathbb E[\sum\langle x_t,g_t\rangle]-\mathbb E[\bar\rho]/(16e^2\theta J)$
-- statement:
--   Throughout, $G=(V,E)$ is a strongly observable directed graph on $K\ge2$ arms ($i\to j$: playing $i$ reveals the loss of $j$), $T\ge3$ is the horizon, and the oblivious adversary fixes losses $\ell_1,\dots,\ell_T\in[0,1]^K$ in advance.
--
--   Suppose $0\in\mathcal B$. For an instance of Algorithm 2 with inputs $A\ge1$ and $0<\theta\le1/(8e)$, started at round $\tau\ge1$ and run on a predictable interval $I$ (in particular an epoch of Algorithm 4, conditionally on the history before its first round),
--   $$
--   \mathbb E_\tau\Big[\sum_{t\in I}\big(\langle x_t,g_t\rangle-g_{t,0}\big)\Big]\le\frac{9\ln(MT)}\theta+12\theta\,\mathbb E_\tau\Big[\sum_{t\in I}\langle x_t,g_t\rangle\Big]-\frac{\mathbb E_\tau[\bar\rho_I]}{16e^2\theta J},
--   $$
--   with $\bar\rho_I=\max_{t\in I}1/x_{t,0}$, $M=|\mathcal B|$, $J=\lceil\log_2(2MT)\rceil$. At $I=[T]$ this is Eq. (29) of Lemma 4.1 with $b=0$.
--
--   Differences from the source:
--   - generalization: the instance of an epoch of Algorithm 4, with $\theta=\theta_{m,\lambda}\le c/\Gamma_A$ → any instance with $0<\theta\le1/(8e)$ on any predictable interval, with no bound on $\mathcal H^{G_{\mathrm{self}}}(q_t)$ assumed; reason: an epoch is such an interval instance and $c/\Gamma_A\le c\le1/(8e)$; the master analysis (proof of Eq. (29), pp.30–31) never uses the bound on $\mathcal H^{G_{\mathrm{self}}}$
--   - encoding: an interval $I$ of rounds, whether $t\in I$ determined before round $t$ is sampled → a continuation predicate on the instance's past arms: round $t\le T$ is in $I$ while it holds; reason: given the history before $\tau$, these are exactly the predictable intervals starting at $\tau$
--   - encoding: conditional expectation $\mathbb E_\tau$ on a filtered probability space → finite sum over the instance's play sequences from round $\tau$ (trajectory law); reason: all randomness is the sequence of played arms; same values
--   - encoding: $\bar\rho_I=\max_{t\in I}1/x_{t,0}$ → $\bar\rho_I=0$ when $I=\emptyset$; reason: the maximum is undefined on $\emptyset$; then both sums and $\bar\rho_I$ are $0$ and the statement reads $0\le9\ln(MT)/\theta$
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, proof of Lemma B.6, p.34 (interval form of Eq. (29), Lemma 4.1, p.11)

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

/-- **The master bound on an epoch (proof of Lemma B.6).** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, proof of Lemma B.6, p.34:
"Applying the proof of Eq. (29) with `b = 0` to the instance of Algorithm 2 for this epoch,
conditionally on the history before `t^start_{m,λ}`, gives
`E_{t^start}[∑_{t ∈ T_{m,λ}} (⟨x_t, g_t⟩ − g_{t,0})] ≤ 9 ln(MT)/θ + 12θ E_{t^start}[∑_{t ∈ T_{m,λ}} ⟨x_t, g_t⟩]
− E_{t^start}[ρ̄_{m,λ}]/(16e²θJ)`."

This is Eq. (29) of Lemma 4.1 (p.11) at `b = 0`, for an instance of Algorithm 2 with `0 ∈ B`,
`θ ≤ 1/(8e)`, run on any predictable interval `I`; at `I = [T]` it is (29) with `b = 0`.

**Formalization Note.** Same encoding of the interval and of `E_τ` as in `lemma_B_1`; `g_t` is
`gvec`, `⟨x, g⟩` is `binner`; `ρ̄ = 0` on an empty interval; `M = |B|`, `ln = Real.log`. -/
theorem epoch_master_bound {K : ℕ} (T : ℕ) (hK : 2 ≤ K) (hT : 3 ≤ T)
    (E : Fin K → Fin K → Prop) [DecidableRel E] (hSO : StronglyObservable E) (ℓ : ℕ → Fin K → ℝ) (hℓ : ∀ t ∈ Finset.Icc 1 T, ∀ i, ℓ t i ∈ Set.Icc (0 : ℝ) 1)
    (q₀ : (Fin K → ℝ) → ℝ → Fin K → ℝ) (hq₀ : InteriorStart E q₀)
    (hB : (Vself E).Nonempty) (τ : ℕ) (hτ : 1 ≤ τ) (A θ : ℝ) (hA : 1 ≤ A) (hθ : 0 < θ)
    (cont : List (Fin K) → Prop) (hθe : θ ≤ 1 / (8 * Real.exp 1)) :
    let st₀ := Alg2.init E A θ
    let Ex := Alg2.condExp E T ℓ q₀ τ st₀
    let sumI := fun F : ℕ → Alg2.State K → ℝ => Ex (fun h => Alg2.sumOn E T ℓ q₀ cont F τ st₀ [] h)
    let r := Ex (fun h => Alg2.maxOn E T ℓ q₀ cont (fun _ st => 1 / st.x none) τ st₀ [] h)
    let M : ℝ := (Bset E).card
    sumI (fun t st => binner E st.x (gvec E (ℓ t) (Alg2.qOf E T q₀ st))
        - gvec E (ℓ t) (Alg2.qOf E T q₀ st) none)
      ≤ 9 * Real.log (M * T) / θ
        + 12 * θ * sumI (fun t st => binner E st.x (gvec E (ℓ t) (Alg2.qOf E T q₀ st)))
        - r / (16 * Real.exp 2 * θ * (Jconst E T : ℝ)) := by sorry

end FirstOrderFG
