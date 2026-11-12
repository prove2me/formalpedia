-- Prove2me | Theorems.Thm_APFB05_support_novel_chain_capacity_bound
-- name    : APFB05.support_novel_chain_capacity_bound
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-12T03:23:44.746939+00:00
-- url     : https://prove2.me/theorems/750aa524-2399-4b8f-b4c0-b98dda31f0ad
-- title:
--   A support-novel chain in an admissible family has at most C/epsilon members
-- statement:
--   Fix a context with capacity $C$ and a positive marginal floor $\varepsilon$ satisfying the declared B05 predicate. Let $S_0,\ldots,S_n$ be finite families with $S_{i+1}=S_i\cup\{d_i\}$. Assume every added distinction is tested and support-novel over its prefix, and the final family is feasible with cost at most $C$. Then
--
--   $$n\varepsilon\le\kappa(S_n),\qquad n\le C/\varepsilon.$$
--
--   This bounds the length of the supplied chain. It assumes neither $S_0=\varnothing$, zero empty-family cost nor attainment. It does not establish a maximal chain rank, the cardinality of the final family, or finiteness of the whole distinction domain. B05 is consumed; no universal bound on every protocol bill is used.
--
--   **Formalization note.** Foundation Inputs revision 2026-10-04.1; independent source review brook-2026-11-12-cold_fidelity_review. Stated hypotheses and representation limits are retained.
-- source:
--   Paper 1 Technical Supplement v9.28 and FOUNDATION_INPUTS.json revision 2026-10-04.1; exact reviewed module Theorems.Thm_APFB05_support_novel_chain_capacity_bound; source SHA256 86dc1194c9d43ddcf36736d4688479c46df8eaaa24ef6c1cf883a3296d167dd8. See the source header for original v9.27 line references and the November 11 testedness ruling.

import Definitions.Def_APFPaper1_FamilyCost
import Definitions.Def_APF_B05_DeclaredInput_r2
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
set_option autoImplicit false
open Classical
open APFPaper1.Source

theorem APFB05.support_novel_chain_capacity_bound
    {Context : Type*} {D P R Record : Context → Type*}
    [∀ g, DecidableEq (D g)]
    (wholeResource : (g : Context) → P g → R g)
    (calibration : (g : Context) → R g → NNReal)
    (maintained : (g : Context) → P g → Set (Record g))
    (sufficient : (g : Context) → P g → Set (Record g) → D g → Prop)
    (usesToRealize : (g : Context) → P g → D g → Set (Record g) → Prop)
    (tested : (g : Context) → D g → Prop)
    (C epsilon : Context → ℝ)
    (hB05 : MarginalFloor wholeResource calibration maintained sufficient usesToRealize tested C epsilon)
    (g : Context) (n : ℕ) (S : ℕ → Finset (D g)) (d : ℕ → D g)
    (hstep : ∀ i < n, S (i + 1) = insert (d i) (S i))
    (htested : ∀ i < n, tested g (d i))
    (hnovel : ∀ i < n, supportNovel (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (S i) (d i))
    (hadm : familyAdmissible (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (C g) (S n)) :
    (n : ℝ) * epsilon g ≤
        familyCost (wholeResource g) (calibration g) (maintained g)
          (sufficient g) (usesToRealize g) (S n) ∧
      (n : ℝ) ≤ C g / epsilon g := by sorry
