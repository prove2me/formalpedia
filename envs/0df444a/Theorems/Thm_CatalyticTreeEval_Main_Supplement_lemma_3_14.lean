-- Prove2me | Theorems.Thm_CatalyticTreeEval_Main_Supplement_lemma_3_14
-- name    : CatalyticTreeEval.Main.Supplement.lemma_3_14
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T19:36:54.753809+00:00
-- url     : https://prove2.me/theorems/aa1ea026-7a29-40e7-9689-46b0aab55e28
-- title:
--   Lemma 3.14 (used in the proof of Theorem 3.4) — least-prime space-bounded selection
-- statement:
--   For every positive integer $D$ supplied in binary, the least prime $p$ in the open interval $(2D,4D)$ exists. One deterministic binary machine prints it, uniformly over $D$, using
--   $$\operatorname{space}\le C L(D).$$
--   Minimality is explicit: $p\le q$ for every prime $q\in(2D,4D)$. This is an algorithmic selection result, rather than just prime existence, and supplies the modulus in the ordinary-space instantiations.
--
--   Differences from the source:
--   - encoding: asymptotic algorithmic resource bounds → a finite binary machine and positive uniform constants, with fixed polynomial degrees where needed; reason: expands O/poly using actual transitions and visited work cells; constants precede varying inputs and tapes
--   - encoding: binary parameters and one-based finite indices → self-delimiting binary headers, zero-based Fin indices and the published printer requests; reason: encodes the same finite data with linear bit-length overhead and no change to the space class
--   - encoding: O(log D) for every positive binary D → C L(D) for every D≥1; reason: handles D=1 without assigning zero space to a halting machine; this is the standard positive-log convention
-- source:
--   Alexandra Henzinger, Edward Pyne, Seyoon Ragavan, Catalytic Tree Evaluation from Matching Vectors, STOC 2027 submission #533 (October 2026), canonical source.pdf SHA-256 17c3a71f0fb5afe2456558477e16fbac4200191e6e68f0facf212e24cb4ef238, Lemma 3.14, printed p. 18 (PDF p. 20)

import Definitions.Def_CatalyticTreeEval_Main_Supplement_UniformConstructions

set_option autoImplicit false

namespace CatalyticTreeEval.Main.Supplement

theorem lemma_3_14 :
    ∃ (M : Machine) (C : ℝ), 0 < C ∧
      ∀ D : ℕ, 0 < D → ∃ p : ℕ,
        LeastIntervalPrime D p ∧ Prints M (natCode D) (natCode p) (C * lg D) := by sorry

end CatalyticTreeEval.Main.Supplement
