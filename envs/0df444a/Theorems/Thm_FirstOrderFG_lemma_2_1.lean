-- Prove2me | Theorems.Thm_FirstOrderFG_lemma_2_1
-- name    : FirstOrderFG.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:46:51.437177+00:00
-- url     : https://prove2.me/theorems/483dd8d2-2f8a-4b44-8133-0b3d0eb13d43
-- title:
--   Lemma 2.1 — $\mathcal H^G(q)\le2\alpha\ln(1+(K^3T+K)/\alpha)+2=O(\alpha\ln(KT))$
-- statement:
--   Throughout, $G=(V,E)$ is a strongly observable directed graph on $K\ge2$ arms ($i\to j$: playing $i$ reveals the loss of $j$), $T\ge3$ is the horizon, and the oblivious adversary fixes losses $\ell_1,\dots,\ell_T\in[0,1]^K$ in advance.
--
--   For every distribution $q\in\Delta_K$,
--   $$
--   \mathcal H^G(q)=\sum_{i\in V_{\mathrm{self}}}\frac{q_i}{Q_i^G(q)+1/(KT)}\ \le\ 2\alpha\ln\Big(1+\frac{K^3T+K}{\alpha}\Big)+2 ,
--   $$
--   and there is a universal constant $C>0$ such that $\mathcal H^G(q)\le C\,\alpha\ln(KT)$ for all such $K,T,G,q$.
--
--   The bound shows that the decision-observation ratio sum, which governs the variance of the loss estimates, is controlled by the independence number up to a logarithmic factor.
--
--   Differences from the source:
--   - encoding: $=O(\alpha\ln(KT))$ → $\exists C>0$ (before all other quantifiers) with $\mathcal H^G(q)\le C\alpha\ln(KT)$; reason: $O(\cdot)$ hides universal constants (p.3)
--   - encoding: horizon $T>2$ → $T\ge3$ ($T\in\mathbb N$); reason: $T$ is an integer; same instances
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Lemma 2.1, p.4

import Mathlib
import Definitions.Def_FirstOrderFG_StronglyObservable
import Definitions.Def_FirstOrderFG_Hgraph
import Definitions.Def_FirstOrderFG_indepNumber

namespace FirstOrderFG

/-- **Lemma 2.1.** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, Lemma 2.1, p.4: "For every distribution `q ∈ ∆_K`, we have
`H^G(q) ≤ 2α ln(1 + (K³T + K)/α) + 2 = O(α ln(KT))`."

Both clauses: the explicit bound, and a universal constant `C` with `H^G(q) ≤ C α ln(KT)`.

**Formalization Note.** Standing assumptions of §2, p.3: `K ≥ 2`, `T > 2` an integer (`T ≥ 3`),
`G` strongly observable; `O(·)` hides a universal constant (p.3), so `∃ C` precedes every other
binder. -/
theorem lemma_2_1 :
    (∀ (K T : ℕ), 2 ≤ K → 3 ≤ T → ∀ (E : Fin K → Fin K → Prop) [DecidableRel E],
      StronglyObservable E → ∀ q : Fin K → ℝ, (∀ i, 0 ≤ q i) → ∑ i, q i = 1 →
        Hgraph E T q ≤ 2 * (indepNumber E : ℝ)
          * Real.log (1 + ((K : ℝ) ^ 3 * T + K) / indepNumber E) + 2) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ (K T : ℕ), 2 ≤ K → 3 ≤ T → ∀ (E : Fin K → Fin K → Prop) [DecidableRel E],
      StronglyObservable E → ∀ q : Fin K → ℝ, (∀ i, 0 ≤ q i) → ∑ i, q i = 1 →
        Hgraph E T q ≤ C * (indepNumber E : ℝ) * Real.log ((K : ℝ) * T) := by sorry

end FirstOrderFG
