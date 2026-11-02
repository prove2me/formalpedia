-- Prove2me | Theorems.Thm_FKZAvg_WStar_lemma_2_fullW
-- name    : FKZAvg.WStar.lemma_2_fullW
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-01T15:15:52.950033+00:00
-- url     : https://prove2.me/theorems/b265d6a0-ace0-4dcc-997d-bc4185012165
-- title:
--   Lemma 2 (corrected) — under (W*), c(x,·) and η^α_u(x,·) are inf-compact on A(x)
-- statement:
--   Lemma 2 of Feinberg–Kasyanov–Zadoianchuk (2012), with the hypothesis that its printed proof silently uses made explicit.
--
--   Let $\mathbb X,\mathbb A$ be the state and action spaces of the model `SchalAvg.AvgOpt.Model` (separable metrizable, standard Borel), with nonempty action sets $A(x)$, a $[0,+\infty]$-valued cost $c$ and a transition probability $q$. For $u:\mathbb X\to[0,+\infty]$ and $\alpha\ge 0$ let
--   $$\eta^\alpha_u(x,a)=c(x,a)+\alpha\int_{\mathbb X}u(y)\,q(dy\mid x,a).\tag{14}$$
--   A function $f$ is *inf-compact on* $U$ if every level set $\{a\in U: f(a)\le\lambda\}$, $\lambda\in\mathbb R$, is compact; $L(\mathbb X)$ is the class of lower semicontinuous functions with nonempty domain $\{x:u(x)<+\infty\}$.
--
--   **Lemma 2 (corrected).** For every $x\in\mathbb X$:
--
--   (a) under Assumptions $(\mathrm W^*(\mathrm i))$ and $(\mathrm W^*(\mathrm{ii}))$, the function $c(x,\cdot)$ is inf-compact on $A(x)$;
--
--   (b) under Assumption $(\mathrm W^*)$, for every $u\in L(\mathbb X)$ and every $\alpha\ge0$, the function $\eta^\alpha_u(x,\cdot)$ is inf-compact on $A(x)$.
--
--   The printed Lemma 2 states (a) under $(\mathrm W^*(\mathrm{ii}))$ alone and (b) under $(\mathrm W^*(\mathrm{ii},\mathrm{iii}))$ alone; both are then false (see the disproof of `FKZAvg.WStar.lemma_2`), because the proof's step "Assumption $(\mathrm W^*(\mathrm{ii}))$ means that this set is compact" needs the closedness supplied by the lower semicontinuity $(\mathrm W^*(\mathrm i))$ of $c$ on $\mathrm{Gr}(A)$. Every use of Lemma 2 in the paper (Lemma 3, Theorem 2, Lemma 7, Theorem 3) is under the full $(\mathrm W^*)$.
-- source:
--   Feinberg, Kasyanov & Zadoianchuk, Average Cost Markov Decision Processes with Weakly Continuous Transition Probabilities, Math. Oper. Res. 37(4) 2012, p. 596, Lemma 2 (with (W*(i)) added, as used by its proof)

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
import Definitions.Def_SchalAvg_AvgOpt_Model
import Definitions.Def_FKZAvg_WStar_Assumptions

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter SchalAvg.AvgOpt

namespace FKZAvg.WStar

/-- Lemma 2 (p. 596), corrected: (a) under (W*(i, ii)), (b) under the full (W*). -/
theorem lemma_2_fullW {X A : Type*}
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] [StandardBorelSpace X]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A] [StandardBorelSpace A]
    (M : Model X A) (hsel : HasSelector M) (x : X) :
    (CondWStar_i M → CondWStar_ii M → InfCompactOn (fun a => M.toMDP.cost x a) (M.Aset x)) ∧
    (CondWStar M →
      ∀ u : X → ℝ≥0∞, InL u → ∀ α : ℝ, 0 ≤ α →
        InfCompactOn (fun a => eta M u α x a) (M.Aset x)) := by sorry

end FKZAvg.WStar
