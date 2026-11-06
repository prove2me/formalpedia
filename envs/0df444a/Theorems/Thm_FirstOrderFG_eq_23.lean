-- Prove2me | Theorems.Thm_FirstOrderFG_eq_23
-- name    : FirstOrderFG.eq_23
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:48:52.605936+00:00
-- url     : https://prove2.me/theorems/c8f713e2-ceac-402e-b6f3-3402dec6155c
-- title:
--   Eq. (23) — one-round fixed-point bound $\langle q_t-p_t,\ell_t\rangle+\mathbb E_t[\cdots]\le\frac{2A\eta_t}{x_{t,0}}g_{t,0}+\frac2T+4\varepsilon$
-- statement:
--   Throughout, $G=(V,E)$ is a strongly observable directed graph on $K\ge2$ arms ($i\to j$: playing $i$ reveals the loss of $j$), $T\ge3$ is the horizon, and the oblivious adversary fixes losses $\ell_1,\dots,\ell_T\in[0,1]^K$ in advance.
--
--   Let $p$ be in the interior of $\Delta(V_{\mathrm{self}})$, $x\in\Delta(\mathcal B)$ with $x_0>0$, $\eta>0$, $\varepsilon=1/(KT^2)$, and let $q$ be an interior point of $\Delta(V_{\mathrm{self}})$ with $\|q-F_{p,\eta/x_0}(q)\|_1\le\varepsilon$ and $\mathcal H^{G_{\mathrm{self}}}(q)\le A$ for some $A\ge1$. Let $\pi$ be the played distribution (18), $\tilde\ell(I)$ the estimate (19) when arm $I$ is played, and $\ell\in[0,1]^K$ the round's losses. Then
--   $$
--   \langle q-p,\ell\rangle+\sum_{I}\pi_I\sum_{i\in V_{\mathrm{self}}}\frac{\eta\,p_i\,\tilde\ell_i(I)^2}{1+\eta\,\tilde\ell_i(I)}\ \le\ \frac{2A\eta}{x_0}\,\langle q,\ell\rangle+\frac2T+4\varepsilon ,
--   $$
--   inner products with $p,q$ being over $V_{\mathrm{self}}$.
--
--   This is the key one-round inequality of the fixed-point sampling rule: the loss-estimation cost is paid by the learner's own loss $g_{t,0}=\langle q_t,\ell_t\rangle$.
--
--   Differences from the source:
--   - generalization: the round-$t$ quantities $p_t,x_t,\eta_t,q_t$ of Algorithm 2 → any $p\in\mathrm{int}\,\Delta(V_{\mathrm{self}})$, $x\in\Delta(\mathcal B)$ with $x_0>0$, $\eta>0$, and interior $\varepsilon$-fixed point $q$ of $F_{p,\eta/x_0}$; reason: the algorithm's quantities have these properties ($p_t\in\mathcal P$, $x_t\in\mathcal X$, $q_t$ from line 6), so it specializes
--   - encoding: $\mathbb E_t[\cdot]$ → finite sum over the played arm $I\sim\pi$; reason: the round's only randomness is $I_t\sim\pi_t$
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Eq. (23), p.9 (proved in App. B.1, Eqs. (65)–(70), pp.22–24)

import Mathlib
import Definitions.Def_FirstOrderFG_StronglyObservable
import Definitions.Def_FirstOrderFG_Bset
import Definitions.Def_FirstOrderFG_fixResidual
import Definitions.Def_FirstOrderFG_epsFix
import Definitions.Def_FirstOrderFG_Hself
import Definitions.Def_FirstOrderFG_piDist
import Definitions.Def_FirstOrderFG_ltilde

namespace FirstOrderFG

/-- **Eq. (23): the one-round fixed-point bound.** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, Eq. (23), p.9: "To tune this adaptive
EXP3 update, we combine the last term of Eq. (2) with the loss discrepancy `⟨q_t − p_t, ℓ_t⟩`
between playing `q_t` and `p_t`, and use the fixed-point construction to show
`⟨q_t − p_t, ℓ_t⟩ + E_t[∑_{i ∈ V_self} η_t p_{t,i} ℓ̃_{t,i}²/(1 + η_t ℓ̃_{t,i})] ≤ (2Aη_t/x_{t,0}) g_{t,0} + 2/T + 4ε`,
where `A` is such that `H^{G_self}(q_t) ≤ A`" (proved in App. B.1, Eqs. (65)–(70), pp.22–24).

Here `p ∈ int ∆(V_self)`, `x ∈ ∆(B)` with `x₀ > 0`, `η > 0`, `q ∈ int ∆(V_self)` is an `ε`-fixed point
of `F_{p, η/x₀}` with `ε = 1/(KT²)`, `1 ≤ A`, `H^{G_self}(q) ≤ A`, `π` is Eq. (18), `E_t` is the sum over
`I ∼ π`, `ℓ̃` is Eq. (19) and `g₀ = ⟨q, ℓ_t⟩`.

**Formalization Note.** The round's quantities `p_t, x_t, η_t, q_t, ℓ_t` are replaced by arbitrary
values with the properties they have in Algorithm 2; inner products with `p, q` are over `V_self`. -/
theorem eq_23 {K : ℕ} (T : ℕ) (hK : 2 ≤ K) (hT : 3 ≤ T)
    (E : Fin K → Fin K → Prop) [DecidableRel E] (hSO : StronglyObservable E)
    (lt : Fin K → ℝ) (hl : ∀ i, lt i ∈ Set.Icc (0 : ℝ) 1)
    (p : Fin K → ℝ) (hp : ∀ i ∈ Vself E, 0 < p i) (hp1 : ∑ i ∈ Vself E, p i = 1)
    (x : Option (Fin K) → ℝ) (hx : ∀ b ∈ Bset E, 0 ≤ x b) (hx' : ∀ b, b ∉ Bset E → x b = 0)
    (hx1 : ∑ b ∈ Bset E, x b = 1) (hx0 : 0 < x none)
    (η : ℝ) (hη : 0 < η) (q : Fin K → ℝ) (hq : ∀ i ∈ Vself E, 0 < q i)
    (hq1 : ∑ i ∈ Vself E, q i = 1) (hfix : fixResidual E T p (η / x none) q ≤ epsFix K T)
    (A : ℝ) (hA : 1 ≤ A) (hH : Hself E T q ≤ A) :
    ∑ i ∈ Vself E, (q i - p i) * lt i
      + ∑ I, piDist E x q I * ∑ i ∈ Vself E,
          η * p i * ltilde E lt (piDist E x q) I i ^ 2 / (1 + η * ltilde E lt (piDist E x q) I i)
      ≤ 2 * A * η / x none * ∑ i ∈ Vself E, q i * lt i + 2 / T + 4 * epsFix K T := by sorry

end FirstOrderFG
