-- Prove2me | Theorems.Thm_APFB07b_no_unique_minimum_with_a_free_side
-- name    : APFB07b.no_unique_minimum_with_a_free_side
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-16T01:52:28.640824+00:00
-- url     : https://prove2.me/theorems/3fe98486-65b3-4b5d-a850-b334d24d56ea
-- title:
--   Same-record opposite partners exclude a unique minimum under record invariance
-- statement:
--   If equal kept records preserve admissibility and cost and every configuration has a same-record opposite-reading partner, there is no unique admissible cost minimum.
--
--   Publication scope: hadm and hcost are additional structural hypotheses. A2 configurations are not identified with potential states or protocols. The conclusion excludes a conjunction of hypotheses; it does not derive ontological absence of a side or quantum superposition.
-- source:
--   ['C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/source/Theorems/Thm_APFB07b_no_side_without_a_record.lean:64 (source SHA256 340bf6da01c499baa0976fa212bdd16e53eb181b791a70a12e8b0a1b565529a7; APFB07b.no_unique_minimum_with_a_free_side)', 'C:/Users/brook/My Drive/__APF Library/Artifacts_2026-11-15_session/astra/sib_v66_publication/reviews/rv2_v66_v22_review.json (SHA256 365ce42aeeada41fa76b7443fe2b5af6017c7fdeb2bb28169266b6dbba622948; modules[Theorems.Thm_APFB07b_no_side_without_a_record].declarations[APFB07b.no_unique_minimum_with_a_free_side])']

import Theorems.Thm_APFB07b_unique_minimum_fixed_by_symmetry
import Theorems.Thm_APFB07b_no_unique_minimum_of_moving_symmetry
import Theorems.Thm_APFB07b_unique_minimum_has_no_side
import Theorems.Thm_APFB07b_B07b_excludes_turnover_symmetry
import Theorems.Thm_APFB07b_unique_minimum_locally_constant_explicit
import Theorems.Thm_APFB07b_unique_minimum_constant_of_finite_explicit
import Theorems.Thm_APFB07b_infinite_of_unique_minimum_changes_explicit
import Theorems.Thm_APFB07b_B07_realized_constant_of_finite_explicit

set_option autoImplicit false
namespace APFB07b
end APFB07b
open APFB07b
variable {Configuration Record : Type*}

theorem APFB07b.no_unique_minimum_with_a_free_side (adm : Configuration → Prop)
    (cost : Configuration → ℝ) (kept : Configuration → Set Record)
    (hadm : ∀ G H, kept G = kept H → adm G → adm H)
    (hcost : ∀ G H, kept G = kept H → cost G = cost H)
    (reads : Configuration → Bool)
    (hfree : ∀ G, ∃ H, kept H = kept G ∧ reads H = !reads G) :
    ¬ ∃ G, IsMinimum adm cost G ∧ ∀ H, IsMinimum adm cost H → H = G := by sorry
