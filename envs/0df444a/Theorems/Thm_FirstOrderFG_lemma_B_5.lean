-- Prove2me | Theorems.Thm_FirstOrderFG_lemma_B_5
-- name    : FirstOrderFG.lemma_B_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:54:18.685486+00:00
-- url     : https://prove2.me/theorems/7ea7687c-f672-4ff0-a1fd-315a2798a2a8
-- title:
--   Lemma B.5 — $\mathbb E_t[\tilde Z_t]=\langle x_t,g_t\rangle$, $0\le\mathcal V_t\le\min\{2\tilde Z_t,5\}$, $\tilde Z_t\le3+1/x_{t,0}$
-- statement:
--   Throughout, $G=(V,E)$ is a strongly observable directed graph on $K\ge2$ arms ($i\to j$: playing $i$ reveals the loss of $j$), $T\ge3$ is the horizon, and the oblivious adversary fixes losses $\ell_1,\dots,\ell_T\in[0,1]^K$ in advance.
--
--   Consider any round $t\le T$ of an instance of Algorithm 2 with inputs $A\ge1$, $\theta>0$, started at round $\tau\ge1$, and let $\tilde Z_t=\langle x_t,\tilde g_t\rangle$ and $\mathcal V_t$ as in Lemma B.3. Then
--   1. $\mathbb E_t[\tilde Z_t]=\langle x_t,g_t\rangle$, the expectation over $I_t\sim\pi_t$;
--   2. for every played arm, $0\le\mathcal V_t\le\min\{2\tilde Z_t,5\}$;
--   3. if $0\in\mathcal B$, then for every played arm, $\tilde Z_t\le3+1/x_{t,0}$.
--
--   These pathwise bounds control the observable loss that triggers the restarts of Algorithm 4, including in the last round of an epoch.
--
--   Differences from the source:
--   - generalization: every round of Algorithm 4 → every round $t\le T$ of every instance of Algorithm 2 with $A\ge1$, $\theta>0$, started at any $\tau\ge1$; reason: each round of Algorithm 4 is a round of such an instance
--   - encoding: $\mathbb E_t[\cdot]$ → finite sum over the played arm $I\sim\pi_t$; reason: the round's only randomness is $I_t$
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Lemma B.5, p.32

import Mathlib
import Definitions.Def_FirstOrderFG_StronglyObservable
import Definitions.Def_FirstOrderFG_InteriorStart
import Definitions.Def_FirstOrderFG_Alg2_runFrom
import Definitions.Def_FirstOrderFG_Alg2_init
import Definitions.Def_FirstOrderFG_binner
import Definitions.Def_FirstOrderFG_gtilde
import Definitions.Def_FirstOrderFG_gvec
import Definitions.Def_FirstOrderFG_Vterm
import Definitions.Def_FirstOrderFG_piDist
import Definitions.Def_FirstOrderFG_Alg2_qOf

namespace FirstOrderFG

/-- **Lemma B.5: pathwise bounds on `V_t` and `Z̃_t`.** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, Lemma B.5, p.32: "For every round
`t`, `E_t[Z̃_t] = ⟨x_t, g_t⟩` and `0 ≤ V_t ≤ min{2Z̃_t, 5}`, where `V_t` is defined in Lemma B.3. If
`0 ∈ B`, then also `Z̃_t ≤ 3 + 1/x_{t,0}`", with `Z̃_t = ⟨x_t, g̃_t⟩` (Algorithm 4, line 11).

Every round `t ≤ T` of every instance of Algorithm 2 with inputs `A ≥ 1`, `θ > 0`, started before
round `τ ≥ 1` (the instances run by Algorithm 4 are of this form): the mean identity with `E_t` the sum
over `I ∼ π_t`, and the bounds for every played arm `I`.

**Formalization Note.** The state before round `t = τ + |h|` is `Alg2.runFrom … τ (Alg2.init E A θ) h`. -/
theorem lemma_B_5 {K : ℕ} (T : ℕ) (hK : 2 ≤ K) (hT : 3 ≤ T)
    (E : Fin K → Fin K → Prop) [DecidableRel E] (hSO : StronglyObservable E) (ℓ : ℕ → Fin K → ℝ) (hℓ : ∀ t ∈ Finset.Icc 1 T, ∀ i, ℓ t i ∈ Set.Icc (0 : ℝ) 1)
    (q₀ : (Fin K → ℝ) → ℝ → Fin K → ℝ) (hq₀ : InteriorStart E q₀)
    (A θ : ℝ) (hA : 1 ≤ A) (hθ : 0 < θ)
    (τ : ℕ) (hτ : 1 ≤ τ) (h : List (Fin K)) (ht : τ + h.length ≤ T) :
    let t := τ + h.length
    let st := Alg2.runFrom E T ℓ q₀ τ (Alg2.init E A θ) h
    let q := Alg2.qOf E T q₀ st
    let Z := fun I : Fin K => binner E st.x (gtilde E (ℓ t) st.x I)
    let V := fun I : Fin K => Vterm E st.x (gtilde E (ℓ t) st.x I)
    ∑ I, piDist E st.x q I * Z I = binner E st.x (gvec E (ℓ t) q) ∧
    (∀ I, 0 ≤ V I ∧ V I ≤ min (2 * Z I) 5) ∧
    ((Vself E).Nonempty → ∀ I, Z I ≤ 3 + 1 / st.x none) := by sorry

end FirstOrderFG
