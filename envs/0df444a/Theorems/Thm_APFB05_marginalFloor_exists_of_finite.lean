-- Prove2me | Theorems.Thm_APFB05_marginalFloor_exists_of_finite
-- name    : APFB05.marginalFloor_exists_of_finite
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-12T03:28:46.270061+00:00
-- url     : https://prove2.me/theorems/f6d34b75-bec1-42ba-acab-e76b6835d2ae
-- title:
--   On finite distinction domains a marginal floor exists without assuming it
-- statement:
--   Assume every context's full distinction domain $D_\Gamma$ is finite. Keep arbitrary source protocol/support/calibrated-bill data, a testedness predicate and a capacity function. There exists a context-dependent positive floor satisfying the guarded B05 predicate:
--
--   $$\exists\varepsilon:\Gamma\mapsto\mathbb R,\quad\operatorname{MarginalFloor}(\varepsilon).$$
--
--   Support novelty supplies a positive gap for each feasible insertion. Finiteness of the full distinction domain makes the collection of such increments finite, so it has a positive lower bound; if the collection is empty, any positive number suffices.
--
--   The finiteness assumption concerns the entire distinction domain, not one finite interrogation. The result gives existence only, with no prescribed numerical value, exact-infimum claim or uniformity across contexts. It consumes neither B03 nor B05 as a physical assumption.
--
--   **Formalization note.** Foundation Inputs revision 2026-10-04.1; independent source review brook-2026-11-12-cold_fidelity_review. Stated hypotheses and representation limits are retained.
-- source:
--   Paper 1 Technical Supplement v9.28 and FOUNDATION_INPUTS.json revision 2026-10-04.1; exact reviewed module Theorems.Thm_APFB05_floor_exists_on_finite_domain; source SHA256 aa3c7dbde6abfc5d26395d85ad8b15797e2e993672cdd085137a28f26184a06d. See the source header for original v9.27 line references and the November 11 testedness ruling.

import Definitions.Def_APF_B05_DeclaredInput_r2
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
set_option autoImplicit false
open Classical
open APFPaper1.Source

theorem APFB05.marginalFloor_exists_of_finite
    {Context : Type*} {D P R Record : Context → Type*}
    [∀ g, DecidableEq (D g)] [∀ g, Finite (D g)]
    (wholeResource : (g : Context) → P g → R g)
    (calibration : (g : Context) → R g → NNReal)
    (maintained : (g : Context) → P g → Set (Record g))
    (sufficient : (g : Context) → P g → Set (Record g) → D g → Prop)
    (usesToRealize : (g : Context) → P g → D g → Set (Record g) → Prop)
    (tested : (g : Context) → D g → Prop)
    (C : Context → ℝ) :
    ∃ epsilon : Context → ℝ,
      MarginalFloor wholeResource calibration maintained sufficient usesToRealize tested C epsilon := by sorry
