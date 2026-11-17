-- Prove2me | Theorems.Thm_FirstOrderFG_Supplement_theorem_3_2
-- name    : FirstOrderFG.Supplement.theorem_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T04:01:48.401727+00:00
-- url     : https://prove2.me/theorems/a3e84b7f-aa35-48b3-a451-d774309b9a79
-- title:
--   Theorem 3.2 — exact and optimized first-order regret for Algorithm 1
-- statement:
--   Let $K\ge2$, $T\ge3$, and let $G$ be a self-aware directed feedback graph on $K$ arms. Fix an oblivious loss sequence $\ell_1,\ldots,\ell_T\in[0,1]^K$. Suppose $A\ge1$ bounds $H^G(q_t)$ on every round of Algorithm 1. For every learning rate satisfying $1/(KT)\le\eta\le1/(12A)$ and every arm $i$,
--
--   $$
--   \operatorname{Reg}^{\mathrm{Alg1}}_{T,i}
--   \le \frac{3\ln K}{\eta}+10A\eta L_{T,i}.
--   $$
--
--   With $\eta=\max\{1/(KT),\min\{1/(12A),\sqrt{\ln K/(AL^\star)}\}\}$, a universal constant $C_1>0$ satisfies
--
--   $$
--   \operatorname{Reg}^{\mathrm{Alg1}}_T
--   \le C_1\bigl(\sqrt{AL^\star\ln K}+A\ln K\bigr).
--   $$
--
--   With the explicit Lemma 2.1 choice of $A$, a universal $C_2>0$ satisfies
--
--   $$
--   \operatorname{Reg}^{\mathrm{Alg1}}_T
--   \le C_2\bigl(\ln(KT)\sqrt{\alpha L^\star}+\ln^2(KT)\alpha\bigr).
--   $$
--
--   Here $\alpha$ is the directed independence number. Both constants are chosen before the graph, horizon, losses, and algorithm run.
--
--   Differences from the source:
--   - encoding: arms [K], rounds [T], conditional expectations, and Algorithm 1 pseudocode → arms Fin K, rounds Finset.Icc 1 T, a finite trajectory law, and explicit deterministic state transitions; reason: Lean encoding of the same oblivious-adversary instances
--   - encoding: O(√(AL⋆ ln K)+A ln K) and Õ(√(αL⋆)+α) → universal constants with respectively the displayed rate and ln(KT), ln²(KT) factors from the proof; reason: asymptotic notation must be a proposition and the proof supplies these logarithmic powers
--   - encoding: √(ln K/(AL⋆)) when L⋆=0 → the value +∞ before the minimum, hence the upper endpoint 1/(12A); reason: preserves the paper's positive-real convention instead of Lean real division's default zero
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Theorem 3.2, p.7

import Mathlib
import Definitions.Def_FirstOrderFG_Supplement_SelfAware
import Definitions.Def_FirstOrderFG_Supplement_Alg1_qOf
import Definitions.Def_FirstOrderFG_Supplement_Alg1_run
import Definitions.Def_FirstOrderFG_Supplement_Alg1_RegK
import Definitions.Def_FirstOrderFG_Supplement_Alg1_Reg
import Definitions.Def_FirstOrderFG_Supplement_Alg1_tunedEta
import Definitions.Def_FirstOrderFG_Supplement_alphaBound
import Definitions.Def_FirstOrderFG_Hgraph
import Definitions.Def_FirstOrderFG_Lk
import Definitions.Def_FirstOrderFG_Lstar
import Definitions.Def_FirstOrderFG_indepNumber

set_option autoImplicit false

namespace FirstOrderFG.Supplement

/-- **Theorem 3.2 (Algorithm 1, exact and optimized first-order regret).**
Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*,
arXiv:2610.40861, Theorem 3.2, p.7.

For every self-aware graph, every bound `A ≥ 1` that controls `H^G(q_t)` on every round,
and `1/(KT) ≤ η ≤ 1/(12A)`, Algorithm 1 satisfies the exact per-arm inequality
`Reg_{T,i} ≤ 3 ln K/η + 10 A η L_{T,i}`. The statement also includes the theorem's
tuned-`η` consequence `O(√(A L⋆ ln K) + A ln K)` and, with the explicit Lemma 2.1
choice of `A`, the full `O(ln(KT)√(αL⋆) + ln²(KT)α)` reading of `Õ(√(αL⋆)+α)`.

**Formalization Note.** `K ≥ 2`, `T ≥ 3`, losses in `[0,1]`, and the oblivious loss
sequence are the standing assumptions of §2. `H^G(q_t) ≤ A` is required after every possible
pre-round history, the pathwise reading of the paper's hypothesis. Algorithm 1 is the complete
finite-tree model `Alg1`: uniform `p₁`, a uniform Picard start on every round, estimates (5),
and the ordinary-simplex update (1). The two constants hidden by `O` and `Õ` are universal
(quantified before `K,T,G,ℓ`). At `L⋆=0`, `Alg1.tunedEta` implements the paper's extended
positive-real convention before taking the minimum. -/
theorem theorem_3_2 :
    ∃ Copt Ctilde : ℝ, 0 < Copt ∧ 0 < Ctilde ∧
      ∀ (K T : ℕ), 2 ≤ K → 3 ≤ T →
      ∀ (E : Fin K → Fin K → Prop) [DecidableRel E], SelfAware E →
      ∀ ℓ : ℕ → Fin K → ℝ,
        (∀ t ∈ Finset.Icc 1 T, ∀ i, ℓ t i ∈ Set.Icc (0 : ℝ) 1) →
        (∀ (A η : ℝ), 1 ≤ A → 1 / ((K : ℝ) * T) ≤ η → η ≤ 1 / (12 * A) →
          (∀ h : List (Fin K), h.length < T →
            FirstOrderFG.Hgraph E T (Alg1.qOf E T (Alg1.run E T ℓ η h)) ≤ A) →
          ∀ i : Fin K,
            Alg1.RegK E T ℓ η i ≤
              3 * Real.log K / η + 10 * A * η * FirstOrderFG.Lk T ℓ i) ∧
        (∀ A : ℝ, 1 ≤ A →
          (∀ h : List (Fin K), h.length < T →
            FirstOrderFG.Hgraph E T
              (Alg1.qOf E T
                (Alg1.run E T ℓ (Alg1.tunedEta K T A (FirstOrderFG.Lstar T ℓ)) h)) ≤ A) →
          Alg1.Reg E T ℓ (Alg1.tunedEta K T A (FirstOrderFG.Lstar T ℓ)) ≤
            Copt * (Real.sqrt (A * FirstOrderFG.Lstar T ℓ * Real.log K) +
              A * Real.log K)) ∧
        Alg1.Reg E T ℓ
            (Alg1.tunedEta K T (alphaBound E T) (FirstOrderFG.Lstar T ℓ)) ≤
          Ctilde *
            (Real.log ((K : ℝ) * T) *
                Real.sqrt (FirstOrderFG.indepNumber E * FirstOrderFG.Lstar T ℓ) +
              Real.log ((K : ℝ) * T) ^ 2 * FirstOrderFG.indepNumber E) := by sorry

end FirstOrderFG.Supplement
