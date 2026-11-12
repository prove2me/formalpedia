-- Prove2me | Theorems.Thm_APFB05_padded_chain_bound
-- name    : APFB05.padded_chain_bound
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-12T03:27:07.041307+00:00
-- url     : https://prove2.me/theorems/21d5d6cd-dd32-459d-b4a3-52bea9a394c5
-- title:
--   Along any chain in an admissible family, the tested support-novel steps each cost at least epsilon
-- statement:
--   Fix a context and a B05 floor $\varepsilon$. Let $S_{i+1}=S_i\cup\{d_i\}$ for $i<n$, with the final family feasible and of cost at most capacity. Let $I_i$ equal one exactly when $d_i$ is tested and support-novel over $S_i$, and zero otherwise. Then
--
--   $$\sum_{i<n} I_i\varepsilon\le\kappa(S_n).$$
--
--   Only the tested, support-novel steps are charged. Other steps are allowed and contribute zero; cost monotonicity into the feasible final family controls them. This result makes no claim that every step is novel or that every protocol is affordable.
--
--   **Formalization note.** Foundation Inputs revision 2026-10-04.1; independent source review brook-2026-11-12-cold_fidelity_review. Stated hypotheses and representation limits are retained.
-- source:
--   Paper 1 Technical Supplement v9.28 and FOUNDATION_INPUTS.json revision 2026-10-04.1; exact reviewed module Theorems.Thm_APFB05_padded_chain_bound; source SHA256 2e6292aaddf1f8bc0d487963c585c836204db175fce67ba91b7632c782fdb83b. See the source header for original v9.27 line references and the November 11 testedness ruling.

import Definitions.Def_APFPaper1_FamilyCost
import Definitions.Def_APF_B05_DeclaredInput_r2
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
set_option autoImplicit false
open Classical
open APFPaper1.Source

theorem APFB05.padded_chain_bound
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
    (hadm : familyAdmissible (wholeResource g) (calibration g) (maintained g)
      (sufficient g) (usesToRealize g) (C g) (S n)) :
    (∑ i ∈ Finset.range n,
        if tested g (d i) ∧ supportNovel (wholeResource g) (calibration g) (maintained g)
            (sufficient g) (usesToRealize g) (S i) (d i)
        then epsilon g else 0) ≤
      familyCost (wholeResource g) (calibration g) (maintained g)
        (sufficient g) (usesToRealize g) (S n) := by sorry
