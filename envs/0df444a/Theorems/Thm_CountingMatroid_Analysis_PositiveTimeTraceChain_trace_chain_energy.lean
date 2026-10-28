-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_PositiveTimeTraceChain_trace_chain_energy
-- name    : CountingMatroid.Analysis.PositiveTimeTraceChain.trace_chain_energy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:36:45.795311+00:00
-- url     : https://prove2.me/theorems/ef9872a4-246c-4109-b9eb-ca43a492db97
-- title:
--   Trace energy equals harmonic-extension energy after mass scaling
-- statement:
--   Let $\Omega$ be a finite state space with decidable equality, $P$ a stochastic transition matrix on $\Omega$, and $A\subseteq\Omega$. Let $R_A(x,y)$ be the uncapped positive-time return kernel: the probability that the first visit to $A$ after at least one transition ends at $y$. Its entries are the increasing limits of finite-horizon return probabilities, retaining any missing mass. Let $R_A^k$ denote ordinary kernel composition, with $R_A^0$ the identity.
--
--   Let $\mu$ be stationary for $P$, assume $\mu(x)>0$ for every $x\in A$, and assume $\mu(A)=\sum_{x\in A}\mu(x)>0$. Define the stochastic trace $T_A=R_A|_{A\times A}$ and the conditional law $\mu_A(x)=\mu(x)/\mu(A)$ on $A$. For a probability distribution $\mu$, use the bilinear form
--   $$\mathcal E_{\mu,P}(f,g)=\sum_{x\in\Omega}\mu(x)f(x)\left(g(x)-\sum_{y\in\Omega}P(x,y)g(y)\right).$$
--   For a function $h:\Omega\to\mathbb R$, its canonical harmonic extension is $H_Ah(x)=\sum_y H_A(x,y)h(y)$, where $H_A(x,y)$ is the probability of first hitting $A$ at $y$, allowing time zero; paths that never hit contribute zero.
--   For every $h:\Omega\to\mathbb R$,
--   $$\mathcal E_{\mu,P}(H_Ah,H_Ah)=\mu(A)\,\mathcal E_{\mu_A,T_A}(h|_A,h|_A).$$
--   This transfers energy calculations between the original chain and its positive-time trace.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/PositiveTimeTraceChain.lean#L95-L120

import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_Dirichlet
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_HittingTime
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_PotentialDecay
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_SpectralGap
import Definitions.Def_CountingMatroidSupport_Probability_Bilinear
import Definitions.Def_CountingMatroidSupport_Probability_FinDist
import Definitions.Def_CountingMatroidSupport_Probability_FinDistFunctional
import Definitions.Def_CountingMatroid_Analysis_PositiveTimeTraceChain
import Definitions.Def_CountingMatroid_Analysis_PositiveTimeTraceHarmonic
import Definitions.Def_CountingMatroid_Analysis_PositiveTimeTraceKernel
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Topology.Order.MonotoneConvergence

namespace Arlib
end Arlib
namespace Arlib.MarkovChains
end Arlib.MarkovChains
namespace Arlib.MarkovChains.FinChain
end Arlib.MarkovChains.FinChain
namespace Arlib.MarkovChains.FinKernel
end Arlib.MarkovChains.FinKernel
namespace Arlib.Probability
end Arlib.Probability
namespace Arlib.Probability.FinDist
end Arlib.Probability.FinDist
namespace Arlib.Probability.FinKernel
end Arlib.Probability.FinKernel
set_option autoImplicit false

/-!
The concrete uncapped positive-time trace as a finite stochastic chain on its
boundary. Its law is the conditional underlying stationary law, and finite
powers agree with the previously constructed return subkernel iterates.
-/
namespace CountingMatroid.Analysis.PositiveTimeTraceChain
end CountingMatroid.Analysis.PositiveTimeTraceChain
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.PositiveTimeTraceChain

open Arlib.Probability Arlib.MarkovChains
open CountingMatroid.Analysis.PositiveTimeTraceKernel
open CountingMatroid.Analysis.PositiveTimeTraceHarmonic

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

theorem CountingMatroid.Analysis.PositiveTimeTraceChain.trace_chain_energy (μ : FinDist Ω) (P : FinChain Ω)
    (hst : Stationary μ P) (A : Finset Ω) (hμ : ∀ x ∈ A, 0 < μ x)
    (hA : 0 < ∑ x ∈ A, μ x) (h : Ω → ℝ) :
    dirichlet μ P (harmonicExtension P A h) (harmonicExtension P A h) =
      (∑ x ∈ A, μ x) * dirichlet (traceLaw μ A hA)
        (traceChain μ P hst A hμ) (fun x => h x) (fun x => h x) := by sorry
