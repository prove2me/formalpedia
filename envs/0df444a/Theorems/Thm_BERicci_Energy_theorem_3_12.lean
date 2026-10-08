-- Prove2me | Theorems.Thm_BERicci_Energy_theorem_3_12
-- name    : BERicci.Energy.theorem_3_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:34:00.776617+00:00
-- url     : https://prove2.me/theorems/2fb5ee2b-ac81-40d6-bff3-e44a0fda60fc
-- title:
--   Theorem 3.12 (first part), p. 36 — under (MD), (ED.b) holds iff every Lipschitz f with bounded support has f ∈ 𝔾 and |Df|² ≥ Γ(f) (3.32)
-- statement:
--   Let $\mathcal E$ be a strongly local symmetric Dirichlet form on $L^2(X,m)$ satisfying (2.1), and let $d$ be a distance on $X$ satisfying condition (MD). Then condition (ED.b) holds if and only if every $f\in\mathrm{Lip}(X,d)$ with bounded support satisfies
--
--   $$f\in\mathbb G,\qquad |Df|^2\ge\Gamma(f)\quad m\text{-a.e. in }X.\tag{3.32}$$
--
--   Here $|Df|$ is the slope of $f$ with respect to $d$. The theorem does not assume that $d$ is the intrinsic distance $d_{\mathcal E}$: it compares an arbitrary distance with the energy through the single condition (ED.b), and is the source of the inequality $2\mathrm{Ch}\ge\mathcal E$ in its second part.
--
--   **Formalization Note** $d$ is the metric of $X$, and $\mathbb L_C$ (in (ED.b)) uses continuity for its topology. Completeness, separability and the Borel σ-algebra of (MD.a) are typeclass binders; full support and (MD.b) are the hypothesis `MD m`. The condition $|Df|^2\ge\Gamma(f)$ is stated for a density $g$ of $\Gamma(f)$, as $g\le|Df|^2$ $m$-a.e. in $[0,\infty]$. Bounded support means that $\{f\neq0\}$ is a bounded set.
-- source:
--   arXiv:1209.5786v4, Theorem 3.12 (first sentence), (3.32), p. 36

import Mathlib
import Definitions.Def_BERicci_Gamma_Setting
import Definitions.Def_BERicci_Energy_Conditions

namespace BERicci.Energy

open MeasureTheory Filter Topology
open scoped ENNReal

/-- **Theorem 3.12** (p. 36), first part: for a strongly local Dirichlet form `E` and the metric `d` of `X`
satisfying (MD), (ED.b) holds iff every Lipschitz `f` with bounded support has `f ∈ 𝔾` and `|Df|² ≥ Γ(f)`
m-a.e. (3.32). -/
theorem theorem_3_12 {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompleteSpace X] [SecondCountableTopology X]
    (m : Measure X) (E : (X → ℝ) → ℝ≥0∞) (hE : BERicci.Gamma.IsDirichletForm m E) (hloc : BERicci.Gamma.IsStronglyLocal m E)
    (hMD : MD m) :
    EDb m E ↔
      ∀ f : X → ℝ, (∃ K, LipschitzWith K f) → Bornology.IsBounded (Function.support f) →
        ∃ g : X → ℝ, BERicci.Gamma.IsCarreDuChamp m E f g ∧ ∀ᵐ x ∂m, ENNReal.ofReal (g x) ≤ BERicci.Gamma.slope f x ^ 2 := by sorry

end BERicci.Energy
