-- Prove2me | Theorems.Thm_APFB07b_infinite_of_unique_minimum_changes_explicit
-- name    : APFB07b.infinite_of_unique_minimum_changes_explicit
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-15T23:28:59.730137+00:00
-- url     : https://prove2.me/theorems/e649fa61-8708-4eed-b336-76bf9296c8f2
-- title:
--   Changing unique minima require infinitely many configurations under these hypotheses
-- statement:
--   With a fixed admissible set, continuous costs, a preconnected parameter space and unique selected minima, different selections at two parameters imply that the configuration type is infinite. No continuum claim follows.
--
--   Publication scope: Expose hadm, hcost, hmove/hflip, fixed adm, continuity, finite Configuration and PreconnectedSpace exactly where used. B07a/B07b wrappers consume their declared forms; A2 source fidelity is not newly certified. Infinite is not continuum; the contradiction does not construct a side-less occupant.
-- source:
--   ['C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/source/Theorems/Thm_APFB07b_unique_minimum_symmetry_and_variation.lean:167 (source SHA256 adf52b438bdaaa3d1639c93dd12ea342c0c189ab1e3ef403254b80debf4d395e; APFB07b.infinite_of_unique_minimum_changes)', 'C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/reviews/rv2_v66_v22_review.json (SHA256 365ce42aeeada41fa76b7443fe2b5af6017c7fdeb2bb28169266b6dbba622948; modules[Theorems.Thm_APFB07b_unique_minimum_symmetry_and_variation].declarations[APFB07b.infinite_of_unique_minimum_changes])']

import Definitions.Def_APF_B07a_DeclaredInput
import Definitions.Def_APF_B07b_DeclaredInput
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Connected.Clopen
set_option autoImplicit false
universe apfNative_u_1 apfNative_u_2

theorem APFB07b.infinite_of_unique_minimum_changes_explicit :
∀ {Lam : Type apfNative_u_1} {Configuration : Type apfNative_u_2} [inst : TopologicalSpace.{apfNative_u_1} Lam]
  [@PreconnectedSpace.{apfNative_u_1} Lam inst] (adm : Configuration → Prop) (cost : Lam → Configuration → Real)
  (hcont :
    ∀ (G : Configuration),
      @Continuous.{apfNative_u_1, 0} Lam Real inst
        (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
        fun (t : Lam) => cost t G)
  (realized : Lam → Configuration)
  (hmin : ∀ (t : Lam), @APFB07b.IsMinimum.{apfNative_u_2} Configuration adm (cost t) (realized t))
  (huniq :
    ∀ (t : Lam) (H : Configuration),
      @APFB07b.IsMinimum.{apfNative_u_2} Configuration adm (cost t) H →
        @Eq.{apfNative_u_2 + 1} Configuration H (realized t))
  (s t : Lam) (hne : @Ne.{apfNative_u_2 + 1} Configuration (realized s) (realized t)),
  Infinite.{apfNative_u_2 + 1} Configuration := by sorry
