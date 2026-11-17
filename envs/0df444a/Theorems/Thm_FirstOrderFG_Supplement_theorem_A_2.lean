-- Prove2me | Theorems.Thm_FirstOrderFG_Supplement_theorem_A_2
-- name    : FirstOrderFG.Supplement.theorem_A_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T04:03:46.766201+00:00
-- url     : https://prove2.me/theorems/68c2c6fa-4cae-4b05-b297-64128924f346
-- title:
--   Theorem A.2 — parameter-free self-aware regret for Algorithm 3
-- statement:
--   Let $K\ge2$, $T\ge3$, and let $G$ be a self-aware directed feedback graph with independence number $\alpha$. For every oblivious loss sequence $\ell_1,\ldots,\ell_T\in[0,1]^K$, there is a universal constant $C>0$ such that Algorithm 3 guarantees, simultaneously for every arm $i$,
--
--   $$
--   \operatorname{Reg}^{\mathrm{Alg3}}_{T,i}
--   \le C\bigl(\ln(KT)\sqrt{\alpha L_{T,i}}+\ln^2(KT)\alpha\bigr),
--   $$
--
--   and therefore
--
--   $$
--   \operatorname{Reg}^{\mathrm{Alg3}}_T
--   \le C\bigl(\ln(KT)\sqrt{\alpha L^\star}+\ln^2(KT)\alpha\bigr).
--   $$
--
--   Algorithm 3 receives only $G$ and $T$: neither $\alpha$ nor $L^\star$ is an input.
--
--   Differences from the source:
--   - encoding: Algorithm 3 pseudocode and its expected regret → explicit deterministic restarts and pre-round while-loops evaluated by a finite trajectory law; reason: Lean encoding of the same oblivious-adversary algorithm, including empty meta-epochs and realized-loss accumulator S
--   - encoding: Õ(√(αL_{T,i})+α) and Õ(√(αL⋆)+α) → one universal constant with ln(KT) on the square-root terms and ln²(KT) on the additive terms; reason: the proof through Eq. (47) and Lemma 2.1 supplies these logarithmic powers
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Theorem A.2, p.15

import Mathlib
import Definitions.Def_FirstOrderFG_Supplement_SelfAware
import Definitions.Def_FirstOrderFG_Supplement_Alg3_RegK
import Definitions.Def_FirstOrderFG_Supplement_Alg3_Reg
import Definitions.Def_FirstOrderFG_Lk
import Definitions.Def_FirstOrderFG_Lstar
import Definitions.Def_FirstOrderFG_indepNumber

set_option autoImplicit false

namespace FirstOrderFG.Supplement

/-- **Theorem A.2 (parameter-free Algorithm 3).** Zhang–Zhang–Luo–Mineiro,
*Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861,
Theorem A.2, p.15.

On every self-aware graph, Algorithm 3 guarantees simultaneously for every arm
`Reg_{T,i} = Õ(√(αL_{T,i})+α)`, and hence
`Reg_T = Õ(√(αL⋆)+α)`, without knowing `α` or `L⋆`. The proof's logarithmic
factors are exposed as `ln(KT)` on the square-root term and `ln²(KT)` on the additive term.

**Formalization Note.** The universal constant precedes every instance parameter. `Alg3` is the
complete printed algorithm: its input is only `G,T`; it permits multiple `A`-doublings before a
round (and hence empty meta-epochs), starts every fresh Algorithm 1 instance uniformly, uses the
printed `max` initialization and floor, and accumulates realized `ℓ_{t,I_t}`. Expected regret is
over the finite tree of arm draws for the oblivious loss sequence. -/
theorem theorem_A_2 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (K T : ℕ), 2 ≤ K → 3 ≤ T →
      ∀ (E : Fin K → Fin K → Prop) [DecidableRel E], SelfAware E →
      ∀ ℓ : ℕ → Fin K → ℝ,
        (∀ t ∈ Finset.Icc 1 T, ∀ i, ℓ t i ∈ Set.Icc (0 : ℝ) 1) →
        (∀ i : Fin K,
          Alg3.RegK E T ℓ i ≤
            C *
              (Real.log ((K : ℝ) * T) *
                  Real.sqrt (FirstOrderFG.indepNumber E * FirstOrderFG.Lk T ℓ i) +
                Real.log ((K : ℝ) * T) ^ 2 * FirstOrderFG.indepNumber E)) ∧
        Alg3.Reg E T ℓ ≤
          C *
            (Real.log ((K : ℝ) * T) *
                Real.sqrt (FirstOrderFG.indepNumber E * FirstOrderFG.Lstar T ℓ) +
              Real.log ((K : ℝ) * T) ^ 2 * FirstOrderFG.indepNumber E) := by sorry

end FirstOrderFG.Supplement
