-- Prove2me | Theorems.Thm_FirstOrderFG_lemma_B_4
-- name    : FirstOrderFG.lemma_B_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:55:00.205203+00:00
-- url     : https://prove2.me/theorems/0c6e76c6-c239-4723-a809-04ad784d9b77
-- title:
--   Lemma B.4 — initial divergence, comparator smoothing, and regularizer changes (82), (83)
-- statement:
--   Throughout, $G=(V,E)$ is a strongly observable directed graph on $K\ge2$ arms ($i\to j$: playing $i$ reveals the loss of $j$), $T\ge3$ is the horizon, and the oblivious adversary fixes losses $\ell_1,\dots,\ell_T\in[0,1]^K$ in advance.
--
--   Consider an instance of Algorithm 2 with inputs $A\ge1$, $\theta>0$; let $M=|\mathcal B|$, $J=\lceil\log_2(2MT)\rceil$ and, for $b\in\mathcal B$, $u^{(b)}=(1-\frac{M-1}{2MT})e_b+\frac1{2MT}\sum_{j\in\mathcal B\setminus\{b\}}e_j\in\mathcal X$. Then:
--   1. $D_{\Psi_1}(u^{(b)},x_1)\le 8\ln(MT)/\theta$ for every $b\in\mathcal B$;
--   2. $\sum_{t=1}^T\langle u^{(b)}-e_b,g_t\rangle\le\frac12$ for every $b\in\mathcal B$ and every sequence $g_t\in[0,1]^{\mathcal B}$;
--   3. pathwise, for every run of the instance (any start round, any played arms) of length $n$ and every $b\in\mathcal B$,
--   $$
--   \sum_{t=1}^{n-1}\big[D_{\Psi_{t+1}}(u^{(b)},x_{t+1})-D_{\Psi_t}(u^{(b)},x_{t+1})\big]\le0; \tag{82}
--   $$
--   4. if $0\in\mathcal B$, pathwise for $b=0$, with $\bar\rho=\max_{1\le t\le n}1/x_{t,0}$,
--   $$
--   \sum_{t=1}^{n-1}\big[D_{\Psi_{t+1}}(u^{(0)},x_{t+1})-D_{\Psi_t}(u^{(0)},x_{t+1})\big]\le-\frac{\bar\rho}{16e^2\theta J}+\frac1{e^2\theta J}. \tag{83}
--   $$
--
--   The negative term in (83), produced by the increasing learning rate of the meta-action, cancels the base learner's dependence on $\bar\rho$.
--
--   Differences from the source:
--   - generalization: $g_t$ the master loss vectors of the run → any sequence $g_t\in[0,1]^{\mathcal B}$; reason: the run's $g_t$ lie in $[0,1]^{\mathcal B}$, so it specializes
--   - generalization: (82), (83) over the $T$ rounds of Algorithm 2 → over every run of an instance from any start round, $T$ replaced by the run's length; reason: specializes to the run from round 1 of length $T$; the paper applies it to epochs (p.35)
--   - encoding: $\bar\rho=\max_t1/x_{t,0}$ → $\bar\rho=0$ for a run of length 0; reason: the maximum is undefined on an empty run; both sides are then $0$ and $1/(e^2\theta J)$
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Lemma B.4, Eqs. (82)–(83), pp.28–29

import Mathlib
import Definitions.Def_FirstOrderFG_StronglyObservable
import Definitions.Def_FirstOrderFG_InteriorStart
import Definitions.Def_FirstOrderFG_Alg2_runFrom
import Definitions.Def_FirstOrderFG_Alg2_init
import Definitions.Def_FirstOrderFG_uComp
import Definitions.Def_FirstOrderFG_binner
import Definitions.Def_FirstOrderFG_DPsi
import Definitions.Def_FirstOrderFG_Jconst

namespace FirstOrderFG

/-- **Lemma B.4: initial divergence, comparator smoothing and regularizer changes.** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861,
Lemma B.4, pp.28–29: "For `b ∈ B`, let `u^{(b)} ≜ (1 − (M−1)/(2MT)) e_b + (1/(2MT)) ∑_{j ∈ B∖{b}} e_j ∈ 𝒳`.
Then `D_{Ψ_1}(u^{(b)}, x_1) ≤ 8 ln(MT)/θ` and `∑_{t=1}^T ⟨u^{(b)} − e_b, g_t⟩ ≤ 1/2`. Moreover,
pathwise, for every `b ∈ B`, `∑_{t=1}^{T−1} [D_{Ψ_{t+1}}(u^{(b)}, x_{t+1}) − D_{Ψ_t}(u^{(b)}, x_{t+1})] ≤ 0`, (82)
and if `0 ∈ B`, then for `b = 0`, the following stronger bound holds:
`∑_{t=1}^{T−1} [D_{Ψ_{t+1}}(u^{(0)}, x_{t+1}) − D_{Ψ_t}(u^{(0)}, x_{t+1})] ≤ −ρ̄/(16e²θJ) + 1/(e²θJ)`. (83)"

All four clauses. The second holds for every sequence `g_t ∈ [0,1]^B`. (82) and (83) hold pathwise
for every run of an instance (from any start round `τ`, on any arms `h`): with `st_j` the state after
`j` rounds, the run's "`T`" is `|h|`, the sums run over `j < |h| − 1`, and `ρ̄ = max_{j < |h|} 1/x_{j,0}`.

**Formalization Note.** `e_b` is the indicator of `b`; `ln = Real.log`; `ρ̄ = 0` for the empty run.
The `θ` of `Ψ_t` on `V̄_self` is the instance's input `θ`. -/
theorem lemma_B_4 {K : ℕ} (T : ℕ) (hK : 2 ≤ K) (hT : 3 ≤ T)
    (E : Fin K → Fin K → Prop) [DecidableRel E] (hSO : StronglyObservable E) (ℓ : ℕ → Fin K → ℝ) (hℓ : ∀ t ∈ Finset.Icc 1 T, ∀ i, ℓ t i ∈ Set.Icc (0 : ℝ) 1)
    (q₀ : (Fin K → ℝ) → ℝ → Fin K → ℝ) (hq₀ : InteriorStart E q₀)
    (A θ : ℝ) (hA : 1 ≤ A) (hθ : 0 < θ) :
    let M : ℝ := (Bset E).card
    let st₁ := Alg2.init E A θ
    (∀ b ∈ Bset E, DPsi E θ θ (uComp E T b) st₁.x ≤ 8 * Real.log (M * T) / θ) ∧
    (∀ b ∈ Bset E, ∀ g : ℕ → Option (Fin K) → ℝ,
      (∀ t ∈ Finset.Icc 1 T, ∀ b' ∈ Bset E, g t b' ∈ Set.Icc (0 : ℝ) 1) →
      ∑ t ∈ Finset.Icc 1 T, binner E (fun b' => uComp E T b b' - if b' = b then 1 else 0) (g t)
        ≤ 1 / 2) ∧
    (∀ (τ : ℕ) (h : List (Fin K)),
      let st := fun j : ℕ => Alg2.runFrom E T ℓ q₀ τ st₁ (h.take j)
      (∀ b ∈ Bset E, ∑ j ∈ Finset.range (h.length - 1),
          (DPsi E (st (j + 1)).θ0 θ (uComp E T b) (st (j + 1)).x
            - DPsi E (st j).θ0 θ (uComp E T b) (st (j + 1)).x) ≤ 0) ∧
      ((Vself E).Nonempty →
        ∑ j ∈ Finset.range (h.length - 1),
          (DPsi E (st (j + 1)).θ0 θ (uComp E T none) (st (j + 1)).x
            - DPsi E (st j).θ0 θ (uComp E T none) (st (j + 1)).x)
        ≤ -(((List.range h.length).map (fun j => 1 / (st j).x none)).foldr max 0)
            / (16 * Real.exp 2 * θ * (Jconst E T : ℝ))
          + 1 / (Real.exp 2 * θ * (Jconst E T : ℝ)))) := by sorry

end FirstOrderFG
