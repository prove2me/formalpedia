-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_eventuallyEq_evalAt_of_meromorphicAt
-- name    : AlgebraicCurve.exists_eventuallyEq_evalAt_of_meromorphicAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/2bff42cd-6b8c-5f49-a47a-92d469d85b45
-- title:
--   Meromorphic functions on the space of places come from F
-- statement:
--   Let $F$ be a field equipped with a $\mathbb{C}$-algebra structure, and assume there is $x \in F$ transcendental over $\mathbb{C}$ with $F$ finite-dimensional over the intermediate field $\mathbb{C}(x) = \mathrm{adjoin}\ \mathbb{C}\ \{x\}$. Assume `IsCurveOver ℂ F`: every nonzero $f \in F$ has a degree-zero divisor whose value at each place is $\mathrm{ord}_v f$, each place has residue field finite-dimensional over $\mathbb{C}$, and $\Omega[F/\mathbb{C}]$ is free of rank one over $F$; here a place is a valuation subring of $F$ containing $\mathbb{C}$, distinct from $F$, which is a principal ideal ring, and $\mathrm{ord}_v f$ is minus the logarithm of its adic valuation of $f$. Suppose the set $X$ of places carries a topology and a charted space structure over $\mathbb{C}$ making it a compact, Hausdorff, connected analytic manifold modelled on $\mathbb{C}$, and (hypothesis `hF`) that for every nonzero $f \in F$ and every $v \in X$ the reading $z \mapsto \mathrm{evalAt}_{\varphi_v^{-1}(z)}(f)$ in the extended chart $\varphi_v$ at $v$ is meromorphic at $\varphi_v(v)$ with meromorphic order there equal to $\mathrm{ord}_v f$, where $\mathrm{evalAt}_w(f)$ is the preimage in $\mathbb{C}$ of the residue of $f$ when $f$ lies in the valuation subring of $w$, and $0$ otherwise. Let $g : X \to \mathbb{C}$ be such that $z \mapsto g(\varphi_v^{-1}(z))$ is meromorphic at $\varphi_v(v)$ for every $v$. Then there exists $f \in F$ such that for every $v$ the two chart readings $z \mapsto g(\varphi_v^{-1}(z))$ and $z \mapsto \mathrm{evalAt}_{\varphi_v^{-1}(z)}(f)$ agree on a punctured neighbourhood of $\varphi_v(v)$.
--
--   This is the one-variable case of the comparison between analytic and algebraic functions (GAGA, or Chow's theorem): the meromorphic functions on the Riemann surface of places of a complex function field $F$ of one variable are exactly the readings of the elements of $F$. It is used in the identification of principal divisors by period conditions ([`AlgebraicCurve.Divisor.isPrincipal_of_forall_pathIntegral_eq_two_pi_I_mul`](thm.html#AlgebraicCurve.Divisor.isPrincipal_of_forall_pathIntegral_eq_two_pi_I_mul)) and in recovering an element of $F$ from a differentiable function on the place space ([`AlgebraicCurve.Place.existsUnique_forall_mem_toValuationSubring_and_evalAt_eq_appLE_of_differentiableAt`](thm.html#AlgebraicCurve.Place.existsUnique_forall_mem_toValuationSubring_and_evalAt_eq_appLE_of_differentiableAt)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_eventuallyEq_evalAt_of_meromorphicAt.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve
open scoped Manifold ContDiff Topology

theorem AlgebraicCurve.exists_eventuallyEq_evalAt_of_meromorphicAt
    (F : Type*) [Field F] [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [CompactSpace (Place ℂ F)]
    [T2Space (Place ℂ F)] [ConnectedSpace (Place ℂ F)]
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
    (g : Place ℂ F → ℂ)
    (hg : ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => g ((extChartAt 𝓘(ℂ, ℂ) v).symm z)) (extChartAt 𝓘(ℂ, ℂ) v v)) :
    ∃ f : F, ∀ v : Place ℂ F,
      (fun z : ℂ => g ((extChartAt 𝓘(ℂ, ℂ) v).symm z)) =ᶠ[𝓝[≠] (extChartAt 𝓘(ℂ, ℂ) v v)]
        (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f) := by sorry
