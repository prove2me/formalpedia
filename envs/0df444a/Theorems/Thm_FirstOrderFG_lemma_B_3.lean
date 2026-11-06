-- Prove2me | Theorems.Thm_FirstOrderFG_lemma_B_3
-- name    : FirstOrderFG.lemma_B_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:54:27.489035+00:00
-- url     : https://prove2.me/theorems/c9066dca-de3d-4097-bcba-33ea592aaaef
-- title:
--   Lemma B.3 — one master step $\langle x_t-u,\tilde g_t\rangle\le D_{\Psi_t}(u,x_t)-D_{\Psi_t}(u,x_{t+1})+2\theta\mathcal V_t$, $\mathbb E_t[\mathcal V_t]\le2\langle x_t,g_t\rangle$
-- statement:
--   Throughout, $G=(V,E)$ is a strongly observable directed graph on $K\ge2$ arms ($i\to j$: playing $i$ reveals the loss of $j$), $T\ge3$ is the horizon, and the oblivious adversary fixes losses $\ell_1,\dots,\ell_T\in[0,1]^K$ in advance.
--
--   Consider any round $t\le T$ of an instance of Algorithm 2 with inputs $A\ge1$ and $0<\theta\le1/8$, started at round $\tau\ge1$. For every $u\in\mathcal X$ and every played arm,
--   $$
--   \langle x_t-u,\tilde g_t\rangle\le D_{\Psi_t}(u,x_t)-D_{\Psi_t}(u,x_{t+1})+2\theta\mathcal V_t, \tag{76}
--   $$
--   and, with $\mathbb E_t$ the expectation over the played arm $I_t\sim\pi_t$,
--   $$
--   \mathbb E_t[\mathcal V_t]\le2\langle x_t,g_t\rangle, \tag{77}
--   $$
--   where $\mathcal V_t=\mathbb I\{0\in\mathcal B\}x_{t,0}^2\tilde g_{t,0}^2+\sum_{i\in\bar V_{\mathrm{self}}}\min\{x_{t,i},(1-x_{t,i})^2\}\tilde g_{t,i}^2$.
--
--   This is the one-step mirror-descent inequality of the hybrid master, with the complement barrier replacing $x_{t,i}$ by $\min\{x_{t,i},(1-x_{t,i})^2\}$.
--
--   Differences from the source:
--   - generalization: rounds of Algorithm 2 (started at round 1) → rounds $t\le T$ of an instance started at any round $\tau\ge1$; reason: $\tau=1$ is the source's case; Algorithm 4 runs instances started at later rounds
--   - encoding: $\mathbb E_t[\cdot]$ → finite sum over the played arm $I\sim\pi_t$; reason: the round's only randomness is $I_t$
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Lemma B.3, Eqs. (76)–(77), p.27

import Mathlib
import Definitions.Def_FirstOrderFG_StronglyObservable
import Definitions.Def_FirstOrderFG_InteriorStart
import Definitions.Def_FirstOrderFG_Alg2_runFrom
import Definitions.Def_FirstOrderFG_Alg2_init
import Definitions.Def_FirstOrderFG_Xset
import Definitions.Def_FirstOrderFG_binner
import Definitions.Def_FirstOrderFG_gtilde
import Definitions.Def_FirstOrderFG_gvec
import Definitions.Def_FirstOrderFG_DPsi
import Definitions.Def_FirstOrderFG_Vterm
import Definitions.Def_FirstOrderFG_piDist

namespace FirstOrderFG

/-- **Lemma B.3: one step of the master.** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, Lemma B.3, p.27: "If `θ ≤ 1/8`, then for
every `u ∈ 𝒳`, `⟨x_t − u, g̃_t⟩ ≤ D_{Ψ_t}(u, x_t) − D_{Ψ_t}(u, x_{t+1}) + 2θV_t`, (76)
`E_t[V_t] ≤ 2⟨x_t, g_t⟩`, (77) where
`V_t ≜ 𝕀{0 ∈ B} x_{t,0}² g̃_{t,0}² + ∑_{i ∈ V̄_self} min{x_{t,i}, (1 − x_{t,i})²} g̃_{t,i}²`."

Every round `t ≤ T` of every instance of Algorithm 2 with inputs `A ≥ 1`, `0 < θ ≤ 1/8`, started
before round `τ ≥ 1`: (76) for every played arm `I` (pathwise), (77) with `E_t` the sum over
`I ∼ π_t`.

**Formalization Note.** The state before round `t = τ + |h|` is `Alg2.runFrom … τ (Alg2.init E A θ) h`;
`x_{t+1}` is the state after `Alg2.step`. `D_{Ψ_t}` uses the current `θ_{t,0}`. -/
theorem lemma_B_3 {K : ℕ} (T : ℕ) (hK : 2 ≤ K) (hT : 3 ≤ T)
    (E : Fin K → Fin K → Prop) [DecidableRel E] (hSO : StronglyObservable E) (ℓ : ℕ → Fin K → ℝ) (hℓ : ∀ t ∈ Finset.Icc 1 T, ∀ i, ℓ t i ∈ Set.Icc (0 : ℝ) 1)
    (q₀ : (Fin K → ℝ) → ℝ → Fin K → ℝ) (hq₀ : InteriorStart E q₀)
    (A θ : ℝ) (hA : 1 ≤ A) (hθ : 0 < θ) (hθ8 : θ ≤ 1 / 8)
    (τ : ℕ) (hτ : 1 ≤ τ) (h : List (Fin K)) (ht : τ + h.length ≤ T) :
    let t := τ + h.length
    let st := Alg2.runFrom E T ℓ q₀ τ (Alg2.init E A θ) h
    let q := Alg2.qOf E T q₀ st
    (∀ u ∈ Xset E T, ∀ I : Fin K,
      binner E (fun b => st.x b - u b) (gtilde E (ℓ t) st.x I)
        ≤ DPsi E st.θ0 θ u st.x - DPsi E st.θ0 θ u (Alg2.step E T ℓ q₀ t st I).x
          + 2 * θ * Vterm E st.x (gtilde E (ℓ t) st.x I)) ∧
    ∑ I, piDist E st.x q I * Vterm E st.x (gtilde E (ℓ t) st.x I)
      ≤ 2 * binner E st.x (gvec E (ℓ t) q) := by sorry

end FirstOrderFG
