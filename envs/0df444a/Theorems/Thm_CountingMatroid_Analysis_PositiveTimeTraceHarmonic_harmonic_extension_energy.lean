-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_PositiveTimeTraceHarmonic_harmonic_extension_energy
-- name    : CountingMatroid.Analysis.PositiveTimeTraceHarmonic.harmonic_extension_energy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:05:13.410532+00:00
-- url     : https://prove2.me/theorems/69157057-e78f-4e65-a976-f7bce26bbedc
-- title:
--   Boundary formula for harmonic-extension energy
-- statement:
--   Let $\Omega$ be a finite state space with decidable equality, $P$ a stochastic transition matrix on $\Omega$, and $A\subseteq\Omega$. Let $R_A(x,y)$ be the uncapped positive-time return kernel: the probability that the first visit to $A$ after at least one transition ends at $y$. Its entries are the increasing limits of finite-horizon return probabilities, retaining any missing mass. Let $R_A^k$ denote ordinary kernel composition, with $R_A^0$ the identity. For a probability distribution $\mu$, use the bilinear form
--   $$\mathcal E_{\mu,P}(f,g)=\sum_{x\in\Omega}\mu(x)f(x)\left(g(x)-\sum_{y\in\Omega}P(x,y)g(y)\right).$$
--   For a function $h:\Omega\to\mathbb R$, its canonical harmonic extension is $H_Ah(x)=\sum_y H_A(x,y)h(y)$, where $H_A(x,y)$ is the probability of first hitting $A$ at $y$, allowing time zero; paths that never hit contribute zero.
--
--   Let $\mu$ be any probability distribution on $\Omega$, and let $f,g:\Omega\to\mathbb R$ be arbitrary functions. Then
--   $$\mathcal E_{\mu,P}(H_Af,H_Ag)=\sum_{x\in A}\mu(x)f(x)\left(g(x)-\sum_{y\in\Omega}R_A(x,y)g(y)\right).$$
--   Neither stationarity nor reversibility of $\mu$ is required. The identity reduces the harmonic-extension bilinear form to a sum on the target boundary.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/PositiveTimeTraceHarmonic.lean#L106-L130

import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_Dirichlet
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_HittingTime
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_PotentialDecay
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_SpectralGap
import Definitions.Def_CountingMatroidSupport_Probability_Bilinear
import Definitions.Def_CountingMatroidSupport_Probability_FinDist
import Definitions.Def_CountingMatroidSupport_Probability_FinDistFunctional
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
Harmonic extension for the concrete positive-time return subkernel. The
extension uses the increasing finite hitting kernels, so the first-step
identities do not assume almost-sure hitting from zero-weight states.
-/
namespace CountingMatroid.Analysis.PositiveTimeTraceHarmonic
end CountingMatroid.Analysis.PositiveTimeTraceHarmonic
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.PositiveTimeTraceHarmonic

open Arlib.Probability Arlib.MarkovChains
open CountingMatroid.Analysis.PositiveTimeTraceKernel

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

theorem CountingMatroid.Analysis.PositiveTimeTraceHarmonic.harmonic_extension_energy (μ : FinDist Ω) (P : FinChain Ω)
    (A : Finset Ω) (f g : Ω → ℝ) :
    dirichlet μ P (harmonicExtension P A f) (harmonicExtension P A g) =
      ∑ x ∈ A, μ x * f x *
        (g x - ∑ y, (uncappedReturn P A).entry x y * g y) := by sorry
