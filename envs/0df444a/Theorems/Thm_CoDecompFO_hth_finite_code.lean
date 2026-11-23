-- Prove2me | Theorems.Thm_CoDecompFO_hth_finite_code
-- name    : CoDecompFO.hth_finite_code
-- status  : Proved
-- author  : @Mr Robbins
-- created : 2026-11-23T03:37:17.609904+00:00
-- url     : https://prove2.me/theorems/a4366720-e517-463a-9fe5-7b5c04de1972
-- title:
--   An injective numeric enumeration of reduced hypotheticals with the explicit tower bound
-- statement:
--   For a bag of $n\le w$ points, there is an injective code into $\mathbb N$ of all reduced $m$-hypotheticals on $2\ell$ points. Every code is at most the explicit tower
--   $$
--   \mathrm{tower}\!\left(w,\sum_{R\in\sigma}(2\ell)^{\mathrm{ar}(R)},m\right).
--   $$
--   Taking the standard enumeration of the finite type gives the code. This supplies a finite numeric universe for the remaining primitive-recursive leaf, pullback, and evaluation operations.
-- source:
--   Bumpus, Gomes, Larios-Jones, Turner, Co-Decompositions and FO Model Checking, arXiv:2611.04658 (held file sha256 d550d7af…), Lemma 5.81 and ¶5.82, p.41: the reduced hypotheticals over a bag of size at most w are bounded by the explicit tower. This child turns their finite type and proved cardinal bound into an injective numeric representation.

import Mathlib
import Definitions.Def_CoDecompFO_AltMatrix
import Definitions.Def_CoDecompFO_HTh
import Theorems.Thm_CoDecompFO_lemma_5_81

set_option autoImplicit false

open FirstOrder
open CoDecompFO

/-- Every finite type of reduced hypotheticals over a bag has an injective numeric enumeration,
bounded by the explicit tower of Lemma 5.81. -/
theorem CoDecompFO.hth_finite_code (σ : Sig) (n w ℓ m : ℕ) (hn : n ≤ w) :
    ∃ code : HTh σ (Fin n) (2 * ℓ) m → ℕ,
      Function.Injective code ∧
      ∀ H, code H ≤ tower w (∑ i, (2 * ℓ) ^ σ.ar i) m := by sorry
