-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_rtj_antidiag_split
-- name    : Formalism.L2.FormalSeriesBounds.rtj_antidiag_split
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:27:32.474077+00:00
-- url     : https://prove2.me/theorems/03bb66b0-aecd-4e30-81bd-9723b88488d9
-- title:
--   Formal Series Bounds: rtj antidiag split
-- statement:
--   The Formal Series Bounds construction uses the rtj antidiag split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieJet.lean#L52-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieJet.lean#L52-L64

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_MemVarsProdAll
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieJet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
variable {K : Type} [Field K] {σ : Type}

theorem Formalism.L2.FormalSeriesBounds.rtj_antidiag_split {A : Set σ} (f g : (σ →₀ ℕ) → K)
    (hf : ∀ c, f c ≠ 0 → (↑c.support : Set σ) ⊆ A)
    (hg : ∀ d, g d ≠ 0 → (↑d.support : Set σ) ⊆ Aᶜ)
    {a b : σ →₀ ℕ} (ha : (↑a.support : Set σ) ⊆ A) (hb : (↑b.support : Set σ) ⊆ Aᶜ) :
    ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (a + b), f x.1 * g x.2 = f a * g b := by sorry
