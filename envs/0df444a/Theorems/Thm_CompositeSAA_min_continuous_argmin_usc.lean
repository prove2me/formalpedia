-- Prove2me | Theorems.Thm_CompositeSAA_min_continuous_argmin_usc
-- name    : CompositeSAA.min_continuous_argmin_usc
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:32:33.664923+00:00
-- url     : https://prove2.me/theorems/29474ed7-2e08-415e-8821-c8f082a6516a
-- title:
--   Proof of Theorem 3, p.6, via [2, Theorem 4.2.2] — continuity of the minimum and upper semicontinuity of the argmin over a compact set
-- statement:
--   Let $\mathcal U\subseteq\mathbb R^n$ be compact, $T$ a topological space and $\Psi:\mathcal U\times T\to\mathbb R$ continuous. Write $S(h)=\{u\in\mathcal U:\Psi(u,h)=\min_{v\in\mathcal U}\Psi(v,h)\}$ for the solution set of the parametric problem (10), $\min_{u\in\mathcal U}\Psi(u,h)$. Then
--
--   1. the optimal value $h\mapsto\min_{u\in\mathcal U}\Psi(u,h)$ is continuous on $T$, and
--   2. the solution map $h\rightrightarrows S(h)$ is upper semicontinuous at every $h_0\in T$: for every open set $V\supseteq S(h_0)$,
--   $$
--   S(h)\subseteq V\quad\text{for all } h \text{ in a neighbourhood of } h_0 .
--   $$
--
--   In the proof of Theorem 3 this is applied with $T=\mathcal H$, the space of level maps, at $h_0=\bar{\mathbf f}^P$; it turns convergence of the level maps into convergence of optimal values and solution sets.
--
--   Differences from the source:
--   - generalization: parameter space $\mathcal H$, a product of spaces of continuous functions with the supremum norm → an arbitrary topological space $T$; reason: $\mathcal H$ is an instance.
--   - reading: the printed "$h\to\min_{u\in U}\Psi(u,h)$" → the minimum over $\mathcal U$; reason: $\Psi$ is defined only on $\mathcal U\times\mathcal H$ and problem (10) minimizes over $\mathcal U$.
--   - encoding: upper semicontinuity → its definition (every open $V\supseteq S(h_0)$ contains $S(h)$ near $h_0$); the minimum is an infimum, attained when $\mathcal U\ne\emptyset$; reason: Lean convention, same instances.
-- source:
--   Dentcheva, Lin, Penev, arXiv:2201.01338v1, proof of Theorem 3, p.6 (citing Bank, Guddat, Klatte, Kummer, Tammer, Non-Linear Parametric Optimization, Theorem 4.2.2)

import Mathlib
import Definitions.Def_CompositeSAA_optimalValue
import Definitions.Def_CompositeSAA_solutionSet

open Filter Topology

namespace CompositeSAA

/-- Dentcheva, Lin, Penev, arXiv:2201.01338v1, proof of Theorem 3, p.6, invoking
[2, Theorem 4.2.2] (Bank, Guddat, Klatte, Kummer, Tammer): let `𝒰 ⊆ ℝ^n` be compact and let
`Ψ` be continuous on `𝒰 × T`. Then

1. the optimal value `h ↦ min_{u ∈ 𝒰} Ψ(u, h)` of the parametric problem (10) is continuous, and
2. the solution map `h ⇉ S(h) = argmin_{u ∈ 𝒰} Ψ(u, h)` is upper semicontinuous at every `h₀`:
   for every open `V ⊇ S(h₀)`, `S(h) ⊆ V` for all `h` near `h₀`.

**Formalization Note** The parameter space is an arbitrary topological space `T`; the paper's is
the normed space `ℋ` of p.5. The minimum is `optimalValue` (an infimum, attained here when
`𝒰 ≠ ∅`) and `S(h)` is `solutionSet`. The printed "`min_{u∈U}`" is the minimum over `𝒰` of (10). -/
theorem min_continuous_argmin_usc {n : ℕ} {T : Type*} [TopologicalSpace T]
    (𝒰 : Set (EuclideanSpace ℝ (Fin n))) (h𝒰 : IsCompact 𝒰)
    (Ψ : EuclideanSpace ℝ (Fin n) → T → ℝ)
    (hΨ : ContinuousOn (fun p : EuclideanSpace ℝ (Fin n) × T => Ψ p.1 p.2) (𝒰 ×ˢ Set.univ)) :
    Continuous (fun h => optimalValue (fun u => Ψ u h) 𝒰) ∧
      ∀ h₀ : T, ∀ V : Set (EuclideanSpace ℝ (Fin n)), IsOpen V →
        solutionSet (fun u => Ψ u h₀) 𝒰 ⊆ V →
          ∀ᶠ h in 𝓝 h₀, solutionSet (fun u => Ψ u h) 𝒰 ⊆ V := by sorry

end CompositeSAA
