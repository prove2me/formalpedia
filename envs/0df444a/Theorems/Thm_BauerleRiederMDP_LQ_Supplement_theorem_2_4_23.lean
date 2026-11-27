-- Prove2me | Theorems.Thm_BauerleRiederMDP_LQ_Supplement_theorem_2_4_23
-- name    : BauerleRiederMDP.LQ.Supplement.theorem_2_4_23
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T23:50:01.782872+00:00
-- url     : https://prove2.me/theorems/5bb373f0-9242-50f9-8754-8fd2b81f443a
-- title:
--   Theorem 2.4.23 — comparison of value functions for ordered transition kernels (st, cv, cx)
-- statement:
--   Suppose a Markov Decision Model with upper bounding function $b$ is given which satisfies the Structure Assumption (SA_N) with the set $IM^\diamond _n$ where $\diamond  \in  {st, cv, cx}$ ($IM_st$, $IM_cv$, $IM_cx$ are the increasing, concave, convex functions in $IB_b^+$). If for all $n = 0, 1, \dots , N - 1$: $Q_n(\cdot |x, a) \le _\diamond  \tilde{Q}_n(\cdot |x, a)$ for all $(x, a) \in  D_n$, then $V_n \le  \tilde V _n$ for $n = 0, 1, \dots , N - 1$, where $\tilde V _n$ are the value functions of the model with transition kernels $\tilde{Q}_n$.
--
--   **Formalization Note.** $E \subset  \mathbb R ^d$ and $A \subset  \mathbb R ^m$ are Borel sets with the componentwise order (§2.4.4, p.35), as subtypes of $Fin d \to  \mathbb R $, $Fin m \to  \mathbb R $; $E$ is not a vector space, and convexity and concavity are the published `ConvexOnVia`, `ConcaveOnVia` along the inclusion. The class $P$ is one of the three; the order $\le _\diamond $ is `KernelOrderLE P` (expectations of the class's functions, whenever they exist; the functions of $IM^\diamond $ may take $-\infty $). The model with $\tilde{Q}$ is $Mt$: it has the same $D_n$, $r_n$, $g_N$ and carries only the standing assumption (A_N); (SA_N) and $b$ are assumed for the original model only. The printed "$(x, a) \in  D$" is $D_n$. Both $V_n$ and $\tilde V _n$ are suprema of path-law values over Markov policies.
--
--   Differences from the source:
--   - encoding: E ⊂ ℝ^d, A ⊂ ℝ^m Borel with the componentwise order → subtypes of Fin d → ℝ, Fin m → ℝ; convexity along the inclusion (published ConvexOnVia/ConcaveOnVia); reason: Lean encoding; same instances
--   - reading: (x,a) ∈ D → (x,a) ∈ D_n; reason: the non-stationary model has the sets D_n; D is the notation of the stationary case
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 2.4.23, p.38 (PDF 53)

import Mathlib
import Definitions.Def_MDPFinance_Bellman_Model
import Definitions.Def_MDPFinance_Bellman_Policy
import Definitions.Def_MDPFinance_Bellman_Operators
import Definitions.Def_MDPFinance_Bellman_History
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_Policy
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_stepKernel
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_pathKernel
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_pathReward
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_markovRule
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_Vpi
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_V
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_deltaN
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_IntegrabilityAssumption
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_IsOptimal
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_TWellDefined
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_StructureAssumption
import Definitions.Def_BauerleRiederMDP_FiniteHorizon_IsUpperBoundingFunction
import Definitions.Def_MDPFinance_Contracting_Model
import Definitions.Def_MDPFinance_Contracting_Bounding
import Definitions.Def_BauerleRiederMDP_ConvexModels_ConvexOnVia
import Definitions.Def_BauerleRiederMDP_ConvexModels_ConcaveOnVia
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_KernelOrderLE

open MeasureTheory ProbabilityTheory
open MDPFinance.Bellman (MarkovDecisionModel)
open MDPFinance.Contracting (IBbPlus)
open BauerleRiederMDP.FiniteHorizon
open BauerleRiederMDP.ConvexModels (ConvexOnVia ConcaveOnVia)

namespace BauerleRiederMDP.LQ.Supplement

/-- **Theorem 2.4.23** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance*
(2011), Theorem 2.4.23, p.38, PDF 53). Suppose a Markov Decision Model with upper bounding function
`b` is given which satisfies the Structure Assumption (SA_N) with the set `IM^⋄_n` where
`⋄ ∈ {st, cv, cx}` (`IM_st`, `IM_cv`, `IM_cx` are the increasing, concave, convex functions in
`IB_b^+`). If for all `n = 0, 1, …, N − 1`: `Q_n(·|x, a) ≤_⋄ Q̃_n(·|x, a)` for all `(x, a) ∈ D_n`, then
`V_n ≤ Ṽ_n` for `n = 0, 1, …, N − 1`, where `Ṽ_n` are the value functions of the model with
transition kernels `Q̃_n`.

**Formalization Note.** `E ⊂ ℝ^d` and `A ⊂ ℝ^m` are Borel sets with the componentwise order
(§2.4.4, p.35), as subtypes of `Fin d → ℝ`, `Fin m → ℝ`; `E` is not a vector space, and convexity and
concavity are the published `ConvexOnVia`, `ConcaveOnVia` along the inclusion. The class `P` is
one of the three; the order `≤_⋄` is `KernelOrderLE P` (expectations of the class's functions,
whenever they exist; the functions of `IM^⋄` may take `−∞`). The model with `Q̃` is `Mt`: it has
the same `D_n`, `r_n`, `g_N` and carries only the standing assumption (A_N); (SA_N) and `b` are
assumed for the original model only. The printed "`(x, a) ∈ D`" is `D_n`. Both `V_n` and `Ṽ_n`
are suprema of path-law values over Markov policies. -/
theorem theorem_2_4_23 {d m N : ℕ} {SE : Set (Fin d → ℝ)} {SA : Set (Fin m → ℝ)}
    (hSE : MeasurableSet SE) (hSA : MeasurableSet SA)
    (M Mt : MarkovDecisionModel SE SA N) (b : SE → ℝ) (hb : IsUpperBoundingFunction M b)
    (P : (SE → EReal) → Prop)
    (hP : P = Monotone ∨ P = ConcaveOnVia Subtype.val Set.univ ∨
      P = ConvexOnVia Subtype.val Set.univ)
    (Deltas : ℕ → Set (SE → SA))
    (hSAN : StructureAssumption M (fun _ => {v | v ∈ IBbPlus b ∧ P v}) Deltas)
    (hANt : IntegrabilityAssumption Mt)
    (hD : ∀ n < N, Mt.D n = M.D n)
    (hr : ∀ n < N, ∀ xa ∈ M.D n, Mt.r n xa = M.r n xa)
    (hg : ∀ x, Mt.g x = M.g x)
    (hQ : ∀ n < N, ∀ xa ∈ M.D n, KernelOrderLE P (M.Q n xa) (Mt.Q n xa)) :
    ∀ n < N, ∀ x, V M n x ≤ V Mt n x := by sorry

end BauerleRiederMDP.LQ.Supplement
