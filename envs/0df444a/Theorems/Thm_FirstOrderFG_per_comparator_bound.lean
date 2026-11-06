-- Prove2me | Theorems.Thm_FirstOrderFG_per_comparator_bound
-- name    : FirstOrderFG.per_comparator_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:03:33.85821+00:00
-- url     : https://prove2.me/theorems/e10d355e-1862-4db3-92e8-006029e7944c
-- title:
--   Proof of Theorem 4.3 — $\mathrm{Reg}_{T,k}=O(\sqrt{\Gamma_{A^\star}\ln(MT)L_{T,k}}+\Gamma_{A^\star}\ln(MT))$
-- statement:
--   Throughout, $G=(V,E)$ is a strongly observable directed graph on $K\ge2$ arms ($i\to j$: playing $i$ reveals the loss of $j$), $T\ge3$ is the horizon, and the oblivious adversary fixes losses $\ell_1,\dots,\ell_T\in[0,1]^K$ in advance.
--
--   There is a universal constant $C>0$ such that the following holds. Let $A^\star\ge1$ satisfy $\mathcal H^{G_{\mathrm{self}}}(q)\le A^\star$ for every $q\in\Delta(V_{\mathrm{self}})$. Then Algorithm 4 satisfies, for every arm $k$,
--   $$
--   \mathrm{Reg}_{T,k}\le C\Big(\sqrt{\Gamma_{A^\star}\ln(MT)\,L_{T,k}}+\Gamma_{A^\star}\ln(MT)\Big),
--   $$
--   with $\Gamma_A=AJ\ln(KT)$, $M=|\mathcal B|$, $J=\lceil\log_2(2MT)\rceil$.
--
--   With $A^\star=O(\alpha\ln(KT))$ from Lemma 2.1 this gives the first-order bound of Theorem 4.3.
--
--   Differences from the source:
--   - encoding: $O(\cdot)$ → $\exists C>0$ before all other quantifiers; reason: $O(\cdot)$ hides universal constants (p.3)
--   - generalization: $A^\star=1$ if $0\notin\mathcal B$ → any $A^\star\ge1$ (the hypothesis on $\mathcal H^{G_{\mathrm{self}}}$ is vacuous when $V_{\mathrm{self}}=\emptyset$); reason: $A^\star=1$ is allowed, so it specializes to the source
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, proof of Theorem 4.3, pp.35–36

import Mathlib
import Definitions.Def_FirstOrderFG_StronglyObservable
import Definitions.Def_FirstOrderFG_InteriorStart
import Definitions.Def_FirstOrderFG_RegK
import Definitions.Def_FirstOrderFG_Lk
import Definitions.Def_FirstOrderFG_GammaA
import Definitions.Def_FirstOrderFG_Hself
import Definitions.Def_FirstOrderFG_Bset

namespace FirstOrderFG

/-- **The per-comparator bound (proof of Theorem 4.3).** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, proof of Theorem 4.3, pp.35–36:
"Let `A⋆ ≥ 1` satisfy `H^{G_self}(q) ≤ A⋆` for every `q ∈ ∆(V_self)`, … and set `A⋆ = 1` if `0 ∉ B`";
"For `Reg_{T,k} > 0`, using `√(x + y) ≤ √x + √y` and the AM–GM inequality, and rearranging, gives
`Reg_{T,k} = O(√(Γ_{A⋆} ln(MT) L_{T,k}) + Γ_{A⋆} ln(MT))` … The case `Reg_{T,k} ≤ 0` is immediate."

There is a universal constant `C` such that Algorithm 4 satisfies, for every `A⋆ ≥ 1` bounding
`H^{G_self}` on `∆(V_self)` and every arm `k`,
`Reg_{T,k} ≤ C(√(Γ_{A⋆} ln(MT) L_{T,k}) + Γ_{A⋆} ln(MT))`.

**Formalization Note.** `∃ C` precedes all other binders (`O(·)` hides a universal constant, p.3).
When `0 ∉ B`, `V_self = ∅` and every `A⋆ ≥ 1` qualifies, including the paper's `A⋆ = 1`.
`Γ_A = AJ ln(KT)`, `M = |B|`, `ln = Real.log`. -/
theorem per_comparator_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (K T : ℕ), 2 ≤ K → 3 ≤ T →
      ∀ (E : Fin K → Fin K → Prop) [DecidableRel E], StronglyObservable E →
      ∀ ℓ : ℕ → Fin K → ℝ, (∀ t ∈ Finset.Icc 1 T, ∀ i, ℓ t i ∈ Set.Icc (0 : ℝ) 1) →
      ∀ q₀ : (Fin K → ℝ) → ℝ → Fin K → ℝ, InteriorStart E q₀ →
      ∀ Astar : ℝ, 1 ≤ Astar →
      (∀ q : Fin K → ℝ, (∀ i ∈ Vself E, 0 ≤ q i) → ∑ i ∈ Vself E, q i = 1 →
        Hself E T q ≤ Astar) →
      ∀ k : Fin K, RegK E T ℓ q₀ k
        ≤ C * (Real.sqrt (GammaA E T Astar * Real.log (((Bset E).card : ℝ) * T) * Lk T ℓ k)
          + GammaA E T Astar * Real.log (((Bset E).card : ℝ) * T)) := by sorry

end FirstOrderFG
