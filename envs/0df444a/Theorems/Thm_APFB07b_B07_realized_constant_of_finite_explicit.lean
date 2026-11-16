-- Prove2me | Theorems.Thm_APFB07b_B07_realized_constant_of_finite_explicit
-- name    : APFB07b.B07_realized_constant_of_finite_explicit
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-15T23:30:41.240016+00:00
-- url     : https://prove2.me/theorems/19137aa1-d1c4-4f3d-a731-76e9cd4513a7
-- title:
--   Declared A2 and BW imply constancy under finite continuous fixed-domain hypotheses
-- statement:
--   If the declared A2 selector and BW unique-minimum predicates hold on a fixed admissible set with finite configurations and continuous costs over a preconnected parameter space, the realized configurations at any two parameters are equal.
--
--   Publication scope: Expose hadm, hcost, hmove/hflip, fixed adm, continuity, finite Configuration and PreconnectedSpace exactly where used. B07a/B07b wrappers consume their declared forms; A2 source fidelity is not newly certified. Infinite is not continuum; the contradiction does not construct a side-less occupant.
-- source:
--   ['C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/source/Theorems/Thm_APFB07b_unique_minimum_symmetry_and_variation.lean:180 (source SHA256 adf52b438bdaaa3d1639c93dd12ea342c0c189ab1e3ef403254b80debf4d395e; APFB07b.B07_realized_constant_of_finite)', 'C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/reviews/rv2_v66_v22_review.json (SHA256 365ce42aeeada41fa76b7443fe2b5af6017c7fdeb2bb28169266b6dbba622948; modules[Theorems.Thm_APFB07b_unique_minimum_symmetry_and_variation].declarations[APFB07b.B07_realized_constant_of_finite])']

import Definitions.Def_APF_B07a_DeclaredInput
import Definitions.Def_APF_B07b_DeclaredInput
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Connected.Clopen
set_option autoImplicit false
universe apfNative_u_1 apfNative_u_2

theorem APFB07b.B07_realized_constant_of_finite_explicit :
∀ {Lam : Type apfNative_u_1} {Configuration : Type apfNative_u_2} [inst : TopologicalSpace.{apfNative_u_1} Lam]
  [@PreconnectedSpace.{apfNative_u_1} Lam inst] [Finite.{apfNative_u_2 + 1} Configuration] (adm : Configuration → Prop)
  (cost : Lam → Configuration → Real)
  (hcont :
    ∀ (G : Configuration),
      @Continuous.{apfNative_u_1, 0} Lam Real inst
        (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
        fun (t : Lam) => cost t G)
  (realized : Lam → Configuration)
  (hA2 :
    @APFB07a.A2Selection.{apfNative_u_1, apfNative_u_2} Lam (fun (x : Lam) => Configuration) (fun (x : Lam) => adm) cost
      realized)
  (hB :
    @APFB07b.BWUniqueMinimum.{apfNative_u_1, apfNative_u_2} Lam (fun (x : Lam) => Configuration) (fun (x : Lam) => adm)
      cost)
  (s t : Lam), @Eq.{apfNative_u_2 + 1} Configuration (realized s) (realized t) := by sorry
